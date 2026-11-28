import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_49149_aux
def packedNat (xs : List Nat) : Nat := xs.foldl (fun a b => Nat.shiftLeft a 64 + b) 0
namespace Logic
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section Gen
variable {α : Type} (A O D : α → α → α)
def Cand (L : List α) (s : α) : Prop :=
  ∃ x ∈ L, ∃ y ∈ L, s = A x y ∨ s = O x y ∨ s = D x y
theorem Cand.mono {L L' : List α} {s : α} (h : ∀ x ∈ L, x ∈ L') :
    Cand A O D L s → Cand A O D L' s := by
  rintro ⟨x, hx, y, hy, h2⟩
  exact ⟨x, h x hx, y, h y hy, h2⟩
theorem consSub {L L' : List α} (h : ∀ x ∈ L, x ∈ L') (s : α) :
    ∀ x ∈ s :: L, x ∈ s :: L' := by
  intro x hx
  simp only [List.mem_cons] at hx ⊢
  exact hx.imp id (h x)
def Reach (T : α) : ℕ → List α → Prop
  | 0, L => T ∈ L
  | k + 1, L => T ∈ L ∨ ∃ s, Cand A O D L s ∧ Reach T k (s :: L)
def ReachN (T : α) : ℕ → List α → List α → Prop
  | 0, L, _ => T ∈ L
  | k + 1, L, F => T ∈ L ∨ ∃ s, Cand A O D L s ∧ s ∉ F ∧ s ∉ L ∧ ReachN T k (s :: L) F
theorem Reach.monoL {T : α} : ∀ (k : ℕ) (L L' : List α), (∀ x ∈ L, x ∈ L') →
    Reach A O D T k L → Reach A O D T k L' := by
  intro k
  induction k with
  | zero => intro L L' h hr; exact h _ hr
  | succ k ih =>
    intro L L' h hr
    rcases hr with h1 | ⟨s, hc, hr⟩
    · exact Or.inl (h _ h1)
    · exact Or.inr ⟨s, hc.mono A O D h, ih _ _ (consSub h s) hr⟩
theorem Reach.monoK {T : α} : ∀ (k : ℕ) (L : List α), Reach A O D T k L →
    Reach A O D T (k + 1) L := by
  intro k
  induction k with
  | zero => intro L hr; exact Or.inl hr
  | succ k ih =>
    intro L hr
    rcases hr with h1 | ⟨s, hc, hr⟩
    · exact Or.inl h1
    · exact Or.inr ⟨s, hc, ih _ hr⟩
theorem Reach.monoLe {T : α} {k k' : ℕ} (h : k ≤ k') (L : List α) (hr : Reach A O D T k L) :
    Reach A O D T k' L := by
  induction h with
  | refl => exact hr
  | step _ ih => exact Reach.monoK A O D _ _ ih
theorem Reach.map {β : Type} (A' O' D' : β → β → β) (φ : α → β)
    (hc : ∀ x y s, (s = A x y ∨ s = O x y ∨ s = D x y) → ∀ L' : List β, φ x ∈ L' →
      φ y ∈ L' → Cand A' O' D' L' (φ s)) {T : α} : ∀ (k : ℕ) (L : List α),
    Reach A O D T k L → Reach A' O' D' (φ T) k (L.map φ) := by
  intro k
  induction k with
  | zero => intro L hr; exact List.mem_map_of_mem hr
  | succ k ih =>
    intro L hr
    rcases hr with h1 | ⟨s, ⟨x, hx, y, hy, hs⟩, hr⟩
    · exact Or.inl (List.mem_map_of_mem h1)
    · exact Or.inr ⟨φ s, hc x y s hs _ (List.mem_map_of_mem hx) (List.mem_map_of_mem hy),
        ih _ hr⟩
theorem ReachN.monoK {T : α} : ∀ (k : ℕ) (L F : List α), ReachN A O D T k L F →
    ReachN A O D T (k + 1) L F := by
  intro k
  induction k with
  | zero => intro L F hr; exact Or.inl hr
  | succ k ih =>
    intro L F hr
    rcases hr with h1 | ⟨s, hc, hf, hl, hr⟩
    · exact Or.inl h1
    · exact Or.inr ⟨s, hc, hf, hl, ih _ _ hr⟩
theorem ReachN.congrL {T : α} : ∀ (k : ℕ) (L L' F : List α), (∀ x, x ∈ L ↔ x ∈ L') →
    ReachN A O D T k L F → ReachN A O D T k L' F := by
  intro k
  induction k with
  | zero => intro L L' F h hr; exact (h _).1 hr
  | succ k ih =>
    intro L L' F h hr
    rcases hr with h1 | ⟨s, hc, hf, hl, hr⟩
    · exact Or.inl ((h _).1 h1)
    · refine Or.inr ⟨s, hc.mono A O D (fun x hx => (h x).1 hx), hf,
        fun hx => hl ((h s).2 hx), ?_⟩
      refine ih _ _ _ ?_ hr
      intro x
      simp only [List.mem_cons, h x]
theorem Reach.toN {T : α} : ∀ (k : ℕ) (L : List α), Reach A O D T k L →
    ReachN A O D T k L [] := by
  intro k
  induction k with
  | zero => intro L hr; exact hr
  | succ k ih =>
    intro L hr
    rcases hr with h1 | ⟨s, hc, hr⟩
    · exact Or.inl h1
    · by_cases hs : s ∈ L
      · refine ReachN.monoK A O D _ _ _ (ih L (Reach.monoL A O D _ _ _ ?_ hr))
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hs
        · exact hx
      · exact Or.inr ⟨s, hc, List.not_mem_nil, hs, ih _ hr⟩
theorem ReachN.dich {T c : α} : ∀ (k : ℕ) (L F : List α), Cand A O D L c → c ∉ L →
    ReachN A O D T k L F →
    ReachN A O D T k L (c :: F) ∨ ∃ k', k = k' + 1 ∧ ReachN A O D T k' (c :: L) F := by
  intro k
  induction k with
  | zero => intro L F _ _ hr; exact Or.inl hr
  | succ k ih =>
    intro L F hc hcL hr
    rcases hr with h1 | ⟨s, hs, hf, hl, hr⟩
    · exact Or.inl (Or.inl h1)
    · by_cases hsc : s = c
      · subst hsc
        exact Or.inr ⟨k, rfl, hr⟩
      · have hc' : Cand A O D (s :: L) c :=
          hc.mono A O D (fun x hx => List.mem_cons_of_mem _ hx)
        have hcL' : c ∉ s :: L := by
          intro hx
          rcases List.mem_cons.mp hx with h | h
          · exact hsc h.symm
          · exact hcL h
        rcases ih (s :: L) F hc' hcL' hr with h | ⟨k', hk, h⟩
        · refine Or.inl (Or.inr ⟨s, hs, ?_, hl, h⟩)
          intro hx
          rcases List.mem_cons.mp hx with h | h
          · exact hsc h
          · exact hf h
        · refine Or.inr ⟨k, rfl, ?_⟩
          subst hk
          refine Or.inr ⟨s, hs.mono A O D (fun x hx => List.mem_cons_of_mem _ hx), hf, ?_, ?_⟩
          · intro hx
            rcases List.mem_cons.mp hx with h | h
            · exact hsc h
            · exact hl h
          · refine ReachN.congrL A O D _ _ _ _ ?_ h
            intro x
            simp only [List.mem_cons]
            tauto
end Gen
abbrev BF (n : ℕ) : Type := (Fin n → Bool) → Bool
abbrev bDiff (a b : Bool) : Bool := a && !b
def x0 (n : ℕ) : Fin n → Bool := fun _ => false
def fT (n : ℕ) : BF n := fun _ => true
def fF (n : ℕ) : BF n := fun _ => false
def fV {n : ℕ} (p : Fin n) : BF n := fun x => x p
def fNot {n : ℕ} (a : BF n) : BF n := fun x => !(a x)
def fBin {n : ℕ} (c : Bool → Bool → Bool) (a b : BF n) : BF n := fun x => c (a x) (b x)
abbrev fAnd {n : ℕ} : BF n → BF n → BF n := fBin and
abbrev fOr {n : ℕ} : BF n → BF n → BF n := fBin or
abbrev fDiff {n : ℕ} : BF n → BF n → BF n := fBin bDiff
abbrev R {n : ℕ} (f : BF n) (k : ℕ) (L : List (BF n)) : Prop := Reach fAnd fOr fDiff f k L
def L0 (n : ℕ) : List (BF n) := fF n :: List.ofFn (fun p : Fin n => fV p)
def ph {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (g : BF n) : BF n :=
  fun z => xor (g (u z)) (g (u (x0 n)))
abbrev nz {n : ℕ} (g : BF n) : BF n := ph id g
theorem nz_cases (c : Bool → Bool → Bool) (hc : c = and ∨ c = or ∨ c = bDiff) (cx cy : Bool) :
    (∀ a b : Bool, xor (c a b) (c cx cy) = and (xor a cx) (xor b cy)) ∨
    (∀ a b : Bool, xor (c a b) (c cx cy) = or (xor a cx) (xor b cy)) ∨
    (∀ a b : Bool, xor (c a b) (c cx cy) = bDiff (xor a cx) (xor b cy)) ∨
    (∀ a b : Bool, xor (c a b) (c cx cy) = bDiff (xor b cy) (xor a cx)) := by
  rcases hc with rfl | rfl | rfl <;> cases cx <;> cases cy <;> decide
theorem ph_bin {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (c : Bool → Bool → Bool)
    (hc : c = and ∨ c = or ∨ c = bDiff) (X Y : BF n) :
    ph u (fBin c X Y) = fAnd (ph u X) (ph u Y) ∨ ph u (fBin c X Y) = fOr (ph u X) (ph u Y) ∨
    ph u (fBin c X Y) = fDiff (ph u X) (ph u Y) ∨
    ph u (fBin c X Y) = fDiff (ph u Y) (ph u X) := by
  rcases nz_cases c hc (X (u (x0 n))) (Y (u (x0 n))) with h | h | h | h
  · exact Or.inl (by funext z; exact h _ _)
  · exact Or.inr (Or.inl (by funext z; exact h _ _))
  · exact Or.inr (Or.inr (Or.inl (by funext z; exact h _ _)))
  · exact Or.inr (Or.inr (Or.inr (by funext z; exact h _ _)))
theorem ph_cand {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (c : Bool → Bool → Bool)
    (hc : c = and ∨ c = or ∨ c = bDiff) (X Y : BF n) (L : List (BF n)) (hX : ph u X ∈ L)
    (hY : ph u Y ∈ L) : Cand fAnd fOr fDiff L (ph u (fBin c X Y)) := by
  rcases ph_bin u c hc X Y with h | h | h | h
  · exact ⟨_, hX, _, hY, Or.inl h⟩
  · exact ⟨_, hX, _, hY, Or.inr (Or.inl h)⟩
  · exact ⟨_, hX, _, hY, Or.inr (Or.inr h)⟩
  · exact ⟨_, hY, _, hX, Or.inr (Or.inr h)⟩
theorem ph_pres {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (x y s : BF n)
    (hs : s = fAnd x y ∨ s = fOr x y ∨ s = fDiff x y) (L : List (BF n)) (hX : ph u x ∈ L)
    (hY : ph u y ∈ L) : Cand fAnd fOr fDiff L (ph u s) := by
  rcases hs with rfl | rfl | rfl
  · exact ph_cand u and (Or.inl rfl) x y L hX hY
  · exact ph_cand u or (Or.inr (Or.inl rfl)) x y L hX hY
  · exact ph_cand u bDiff (Or.inr (Or.inr rfl)) x y L hX hY
theorem nz_F {n : ℕ} : nz (fF n) = fF n := rfl
theorem nz_T {n : ℕ} : nz (fT n) = fF n := rfl
theorem nz_not {n : ℕ} (w : BF n) : nz (fNot w) = nz w := by
  funext z
  show xor (!(w z)) (!(w (x0 n))) = xor (w z) (w (x0 n))
  cases w z <;> cases w (x0 n) <;> rfl
def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false
def cnt : List Gate → ℕ
  | [] => 0
  | g :: gs => cond (isNot g.op) (cnt gs) (cnt gs + 1)
theorem cnt_le : ∀ gs : List Gate, cnt gs ≤ gs.length := by
  intro gs
  induction gs with
  | nil => exact Nat.le_refl _
  | cons g gs ih =>
    show cond (isNot g.op) (cnt gs) (cnt gs + 1) ≤ gs.length + 1
    cases isNot g.op
    · exact Nat.succ_le_succ ih
    · exact Nat.le_succ_of_le ih
theorem cnt_lt : ∀ gs : List Gate, (∃ g ∈ gs, g.op = GateOp.not) → cnt gs + 1 ≤ gs.length := by
  intro gs
  induction gs with
  | nil => rintro ⟨g, hg, _⟩; exact absurd hg List.not_mem_nil
  | cons g gs ih =>
    rintro ⟨g', hg', hn⟩
    show cond (isNot g.op) (cnt gs) (cnt gs + 1) + 1 ≤ gs.length + 1
    rcases List.mem_cons.mp hg' with rfl | hg'
    · rw [hn]
      exact Nat.succ_le_succ (cnt_le gs)
    · have := ih ⟨g', hg', hn⟩
      have h2 := cnt_le gs
      cases isNot g.op
      · exact Nat.succ_le_succ this
      · exact Nat.succ_le_succ h2
def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def wf {n : ℕ} (W : List (BF n)) (i : ℕ) : BF n := fun x => (W.map (fun w => w x)).getD i false
def gf {n : ℕ} (W : List (BF n)) (g : Gate) : BF n :=
  fun x => g.op.eval (g.inputs.map fun i => (W.map (fun w => w x)).getD i false)
theorem wf_mem {n : ℕ} {W L : List (BF n)} (hF : fF n ∈ L) (hW : ∀ w ∈ W, nz w ∈ L) (i : ℕ) :
    nz (wf W i) ∈ L := by
  by_cases h : i < W.length
  · have e : wf W i = W[i] := by
      funext x
      simp [wf, List.getD_eq_getElem?_getD, h]
    rw [e]
    exact hW _ (List.getElem_mem h)
  · have e : wf W i = fF n := by
      funext x
      have : W.length ≤ i := not_lt.mp h
      simp [wf, fF, List.getD_eq_getElem?_getD, this]
    rw [e]
    exact hF
theorem gf_step {n : ℕ} {W L : List (BF n)} (hF : fF n ∈ L) (hW : ∀ w ∈ W, nz w ∈ L)
    (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    nz (gf W g) ∈ L ∨ (isNot g.op = false ∧ Cand fAnd fOr fDiff L (nz (gf W g))) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  have hm := fun i => wf_mem hF hW i
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · left
    rcases hop with rfl | rfl | rfl
    · have e : gf W ⟨GateOp.and, []⟩ = fT n := by funext x; simp [gf, GateOp.eval, fT]
      rw [e]; exact hF
    · have e : gf W ⟨GateOp.or, []⟩ = fF n := by funext x; simp [gf, GateOp.eval, fF]
      rw [e]; exact hF
    · have e : gf W ⟨GateOp.not, []⟩ = fT n := by funext x; simp [gf, GateOp.eval, fT]
      rw [e]; exact hF
  · left
    rcases hop with rfl | rfl | rfl
    · have e : gf W ⟨GateOp.and, [a]⟩ = wf W a := by funext x; simp [gf, GateOp.eval, wf]
      rw [e]; exact hm a
    · have e : gf W ⟨GateOp.or, [a]⟩ = wf W a := by funext x; simp [gf, GateOp.eval, wf]
      rw [e]; exact hm a
    · have e : gf W ⟨GateOp.not, [a]⟩ = fNot (wf W a) := by
        funext x; simp [gf, GateOp.eval, wf, fNot]
      rw [e, nz_not]; exact hm a
  · rcases hop with rfl | rfl | rfl
    · right
      have e : gf W ⟨GateOp.and, [a, b]⟩ = fBin and (wf W a) (wf W b) := by
        funext x; simp [gf, GateOp.eval, wf, fBin]
      rw [e]
      exact ⟨rfl, ph_cand id and (Or.inl rfl) _ _ L (hm a) (hm b)⟩
    · right
      have e : gf W ⟨GateOp.or, [a, b]⟩ = fBin or (wf W a) (wf W b) := by
        funext x; simp [gf, GateOp.eval, wf, fBin]
      rw [e]
      exact ⟨rfl, ph_cand id or (Or.inr (Or.inl rfl)) _ _ L (hm a) (hm b)⟩
    · left
      have e : gf W ⟨GateOp.not, [a, b]⟩ = fNot (wf W a) := by
        funext x; simp [gf, GateOp.eval, wf, fNot]
      rw [e, nz_not]; exact hm a
  · simp at hlen
theorem prog_of_gates {n : ℕ} : ∀ (gs : List Gate) (W L : List (BF n)), fF n ∈ L →
    (∀ w ∈ W, nz w ∈ L) →
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    ∀ o : ℕ, R (nz (fun x => (gs.foldl stepW (W.map (fun w => w x))).getD o false))
      (cnt gs) L := by
  intro gs
  induction gs with
  | nil =>
    intro W L hF hW _ o
    exact wf_mem hF hW o
  | cons g gs ih =>
    intro W L hF hW hg o
    have e : (fun x : Fin n → Bool =>
          ((g :: gs).foldl stepW (W.map (fun w => w x))).getD o false)
        = (fun x => (gs.foldl stepW ((W ++ [gf W g]).map (fun w => w x))).getD o false) := by
      funext x
      simp [stepW, gf]
    rw [e]
    have hg' := fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')
    show R _ (cond (isNot g.op) (cnt gs) (cnt gs + 1)) L
    rcases gf_step hF hW g (hg g List.mem_cons_self) with hin | ⟨hn, hc⟩
    · have h := ih (W ++ [gf W g]) L hF (by
        intro w hw
        rcases List.mem_append.mp hw with h | h
        · exact hW w h
        · simp only [List.mem_singleton] at h
          rw [h]; exact hin) hg' o
      cases isNot g.op
      · exact Reach.monoK fAnd fOr fDiff _ _ h
      · exact h
    · rw [hn]
      refine Or.inr ⟨nz (gf W g), hc, ?_⟩
      refine ih (W ++ [gf W g]) (nz (gf W g) :: L) (List.mem_cons_of_mem _ hF) ?_ hg' o
      intro w hw
      rcases List.mem_append.mp hw with h | h
      · exact List.mem_cons_of_mem _ (hW w h)
      · simp only [List.mem_singleton] at h
        rw [h]; exact List.mem_cons_self
theorem prog_of_gatelist {n : ℕ} (f : BF n) (gates : List Gate) (o : ℕ)
    (hok : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (he : ∀ x : Fin n → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x) :
    R (nz f) (cnt gates) (L0 n) := by
  have e : f = (fun x => (gates.foldl stepW
      ((List.ofFn (fun p : Fin n => fV p)).map (fun w => w x))).getD o false) := by
    funext x
    rw [← he x]
    have e2 : (List.ofFn (fun p : Fin n => fV p)).map (fun w => w x) = List.ofFn x := by
      rw [List.map_ofFn]; rfl
    rw [e2]
    rfl
  rw [e]
  refine prog_of_gates gates _ (L0 n) List.mem_cons_self ?_ hok o
  intro w hw
  obtain ⟨q, rfl⟩ := (List.mem_ofFn' _ _).mp hw
  have e3 : nz (fV q) = fV q := by
    funext z
    show xor (z q) false = z q
    cases z q <;> rfl
  rw [e3]
  exact List.mem_cons_of_mem _ ((List.mem_ofFn' _ _).mpr ⟨q, rfl⟩)
def upd {n : ℕ} (p : Fin n) (b : Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i = p then b else x i
def rho {n : ℕ} (p : Fin n) (b : Bool) (g : BF n) : BF n := fun x => g (upd p b x)
abbrev phi {n : ℕ} (p : Fin n) (b : Bool) (g : BF n) : BF n := ph (upd p b) g
def Fix {n : ℕ} (p : Fin n) (g : BF n) : Prop := (∀ b, rho p b g = g) ∧ g (x0 n) = false
def Good {n : ℕ} (p : Fin n) (L : List (BF n)) : Prop :=
  fF n ∈ L ∧ ∀ g ∈ L, g = fV p ∨ Fix p g
theorem fix_phi {n : ℕ} {p : Fin n} {g : BF n} (h : Fix p g) (b : Bool) : phi p b g = g := by
  funext z
  have h1 := congrFun (h.1 b) z
  have h2 := congrFun (h.1 b) (x0 n)
  simp only [rho] at h1 h2
  show xor (g (upd p b z)) (g (upd p b (x0 n))) = g z
  rw [h1, h2, h.2]
  cases g z <;> rfl
theorem upd_self {n : ℕ} (p : Fin n) (b : Bool) (w : Fin n → Bool) : upd p b w p = b := by
  simp [upd]
theorem phi_var {n : ℕ} (p : Fin n) (b : Bool) : phi p b (fV p) = fF n := by
  funext z
  show xor (upd p b z p) (upd p b (x0 n) p) = false
  rw [upd_self, upd_self]
  cases b <;> rfl
theorem fix_bin {n : ℕ} {p : Fin n} (c : Bool → Bool → Bool) (hc0 : c false false = false)
    {x y : BF n} (hx : Fix p x) (hy : Fix p y) : Fix p (fBin c x y) := by
  refine ⟨fun b => ?_, ?_⟩
  · show fBin c (rho p b x) (rho p b y) = _
    rw [hx.1 b, hy.1 b]
  · show c (x (x0 n)) (y (x0 n)) = false
    rw [hx.2, hy.2, hc0]
theorem xor_false_eq (a b : Bool) (h : xor a b = false) : a = b := by
  revert h; cases a <;> cases b <;> decide
theorem un_const (g : Bool → Bool) (h : g true = g false) (a b : Bool) :
    xor (g a) (g b) = false := by
  cases a <;> cases b <;> simp [h]
theorem un_inj (g : Bool → Bool) (h : ¬ g true = g false) (a b : Bool) :
    xor (g a) (g b) = xor a b := by
  cases a <;> cases b <;> revert h <;> cases g true <;> cases g false <;> decide
theorem absorb_l {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (c : Bool → Bool → Bool)
    (X Y : BF n) (h : ph u X = fF n) :
    ph u (fBin c X Y) = fF n ∨ ph u (fBin c X Y) = ph u Y := by
  have hX : ∀ z, X (u z) = X (u (x0 n)) := fun z => xor_false_eq _ _ (congrFun h z)
  by_cases hcc : c (X (u (x0 n))) true = c (X (u (x0 n))) false
  · left
    funext z
    show xor (c (X (u z)) (Y (u z))) (c (X (u (x0 n))) (Y (u (x0 n)))) = false
    rw [hX z]
    exact un_const (c (X (u (x0 n)))) hcc _ _
  · right
    funext z
    show xor (c (X (u z)) (Y (u z))) (c (X (u (x0 n))) (Y (u (x0 n))))
      = xor (Y (u z)) (Y (u (x0 n)))
    rw [hX z]
    exact un_inj (c (X (u (x0 n)))) hcc _ _
theorem absorb_r {n : ℕ} (u : (Fin n → Bool) → (Fin n → Bool)) (c : Bool → Bool → Bool)
    (X Y : BF n) (h : ph u Y = fF n) :
    ph u (fBin c X Y) = fF n ∨ ph u (fBin c X Y) = ph u X :=
  absorb_l u (fun a b => c b a) Y X h
theorem Good.cons {n : ℕ} {p : Fin n} {L : List (BF n)} (h : Good p L) {t : BF n}
    (ht : Fix p t) : Good p (t :: L) := by
  obtain ⟨h2, h3⟩ := h
  refine ⟨List.mem_cons_of_mem _ h2, ?_⟩
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact Or.inr ht
  · exact h3 g hg
theorem phase2 {n : ℕ} (p : Fin n) (b : Bool) (f : BF n) (h1 : phi p b f ≠ fF n)
    (h3 : ¬ ∀ b, rho p b f = f) : ∀ (k : ℕ) (L : List (BF n)) (s : BF n),
    Good p L → phi p b s = fF n → R f k (s :: L) →
    ∃ k', k = k' + 1 ∧ R (phi p b f) k' L := by
  have hmemF : ∀ (L : List (BF n)) (s : BF n), Good p L → phi p b s = fF n →
      f ∈ s :: L → False := by
    intro L s hG hs hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h1 hs
    · rcases hG.2 f hf with rfl | h
      · exact h1 (phi_var p b)
      · exact h3 h.1
  intro k
  induction k with
  | zero => intro L s hG hs hr; exact (hmemF L s hG hs hr).elim
  | succ k ih =>
    intro L s hG hs hr
    rcases hr with hr | ⟨t, ⟨x, hx, y, hy, ht⟩, hr⟩
    · exact (hmemF L s hG hs hr).elim
    · obtain ⟨hGF, hGall⟩ := hG
      have cls : ∀ z ∈ s :: L, phi p b z = fF n ∨ (z ∈ L ∧ Fix p z) := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inl hs
        · rcases hGall z hz with rfl | h
          · exact Or.inl (phi_var p b)
          · exact Or.inr ⟨hz, h⟩
      have rmem : ∀ z ∈ s :: L, phi p b z ∈ L := by
        intro z hz
        rcases cls z hz with h | ⟨h, hi⟩
        · rw [h]; exact hGF
        · rw [fix_phi hi b]; exact h
      have red : phi p b t ∈ L → ∃ k', k + 1 = k' + 1 ∧ R (phi p b f) k' L := by
        intro htL
        refine ⟨k, rfl, ?_⟩
        have hm := Reach.map fAnd fOr fDiff fAnd fOr fDiff (phi p b) (ph_pres (upd p b)) k _ hr
        refine Reach.monoL fAnd fOr fDiff _ _ _ ?_ hm
        intro z hz
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        rcases List.mem_cons.mp hw with rfl | hw
        · exact htL
        · exact rmem w hw
      have keep : Cand fAnd fOr fDiff L t → Fix p t →
          ∃ k', k + 1 = k' + 1 ∧ R (phi p b f) k' L := by
        intro hc hi
        have hr' : R f k (s :: t :: L) := by
          refine Reach.monoL fAnd fOr fDiff _ _ _ ?_ hr
          intro z hz
          simp only [List.mem_cons] at hz ⊢
          tauto
        obtain ⟨k', rfl, h⟩ := ih (t :: L) s (Good.cons ⟨hGF, hGall⟩ hi) hs hr'
        exact ⟨k' + 1, rfl, Or.inr ⟨t, hc, h⟩⟩
      have main : ∀ c : Bool → Bool → Bool, c false false = false → t = fBin c x y →
          (x ∈ L → y ∈ L → Cand fAnd fOr fDiff L t) →
          ∃ k', k + 1 = k' + 1 ∧ R (phi p b f) k' L := by
        intro c hc0 e hcand
        rcases cls x hx with hxc | ⟨hxL, hxi⟩
        · apply red
          rw [e]
          show ph (upd p b) (fBin c x y) ∈ L
          rcases (absorb_l (upd p b) c x y hxc :
              phi p b (fBin c x y) = fF n ∨ phi p b (fBin c x y) = phi p b y) with h | h
          · rw [h]; exact hGF
          · rw [h]; exact rmem y hy
        · rcases cls y hy with hyc | ⟨hyL, hyi⟩
          · apply red
            rw [e]
            show ph (upd p b) (fBin c x y) ∈ L
            rcases (absorb_r (upd p b) c x y hyc :
                phi p b (fBin c x y) = fF n ∨ phi p b (fBin c x y) = phi p b x) with h | h
            · rw [h]; exact hGF
            · rw [h]; exact rmem x hx
          · exact keep (hcand hxL hyL) (e ▸ fix_bin c hc0 hxi hyi)
      rcases ht with e | e | e
      · exact main and rfl e (fun a b => ⟨x, a, y, b, Or.inl e⟩)
      · exact main or rfl e (fun a b => ⟨x, a, y, b, Or.inr (Or.inl e)⟩)
      · exact main bDiff rfl e (fun a b => ⟨x, a, y, b, Or.inr (Or.inr e)⟩)
theorem one_gate {n : ℕ} (p : Fin n) (b : Bool) (f : BF n) (h1 : phi p b f ≠ fF n)
    (h3 : ¬ ∀ b, rho p b f = f) (k : ℕ) (L : List (BF n)) (hG : Good p L)
    (hr : R f k L) : ∃ k', k = k' + 1 ∧ R (phi p b f) k' L := by
  refine phase2 p b f h1 h3 k L (fF n) hG rfl ?_
  exact Reach.monoL fAnd fOr fDiff _ _ _ (fun x hx => List.mem_cons_of_mem _ hx) hr
theorem kill_l {n : ℕ} (p : Fin n) (b : Bool) (c : Bool → Bool → Bool)
    (hc : c b true = c b false) (y : BF n) : phi p b (fBin c (fV p) y) = fF n := by
  funext z
  show xor (c (upd p b z p) (y (upd p b z))) (c (upd p b (x0 n) p) (y (upd p b (x0 n)))) = false
  rw [upd_self, upd_self]
  exact un_const (c b) hc _ _
theorem kill_r {n : ℕ} (p : Fin n) (b : Bool) (c : Bool → Bool → Bool)
    (hc : c true b = c false b) (y : BF n) : phi p b (fBin c y (fV p)) = fF n :=
  kill_l p b (fun a d => c d a) hc y
theorem two_gates {n : ℕ} (p : Fin n) (f : BF n) (h0 : phi p false f ≠ fF n)
    (h1 : phi p true f ≠ fF n) (h3 : ¬ ∀ b, rho p b f = f) :
    ∀ (k : ℕ) (L : List (BF n)), Good p L → R f k L →
    ∃ k', k = k' + 2 ∧ (R (phi p false f) k' L ∨ R (phi p true f) k' L) := by
  have hmemF : ∀ (L : List (BF n)), Good p L → f ∈ L → False := by
    intro L hG hf
    rcases hG.2 f hf with rfl | h
    · exact h0 (phi_var p false)
    · exact h3 h.1
  intro k
  induction k with
  | zero => intro L hG hr; exact (hmemF L hG hr).elim
  | succ k ih =>
    intro L hG hr
    rcases hr with hr | ⟨t, ⟨x, hx, y, hy, ht⟩, hr⟩
    · exact (hmemF L hG hr).elim
    · have keep : Fix p t → ∃ k', k + 1 = k' + 2 ∧
          (R (phi p false f) k' L ∨ R (phi p true f) k' L) := by
        intro hi
        obtain ⟨k', rfl, h⟩ := ih (t :: L) (Good.cons hG hi) hr
        refine ⟨k' + 1, rfl, ?_⟩
        rcases h with h | h
        · exact Or.inl (Or.inr ⟨t, ⟨x, hx, y, hy, ht⟩, h⟩)
        · exact Or.inr (Or.inr ⟨t, ⟨x, hx, y, hy, ht⟩, h⟩)
      have kill : ∀ b : Bool, phi p b t = fF n → ∃ k', k + 1 = k' + 2 ∧
          (R (phi p false f) k' L ∨ R (phi p true f) k' L) := by
        intro b hc
        cases b
        · obtain ⟨k', rfl, h⟩ := phase2 p false f h0 h3 k L t hG hc hr
          exact ⟨k', rfl, Or.inl h⟩
        · obtain ⟨k', rfl, h⟩ := phase2 p true f h1 h3 k L t hG hc hr
          exact ⟨k', rfl, Or.inr h⟩
      have main : ∀ (c : Bool → Bool → Bool) (bl br : Bool), c false false = false →
          c bl true = c bl false → c true br = c false br → t = fBin c x y →
          ∃ k', k + 1 = k' + 2 ∧ (R (phi p false f) k' L ∨ R (phi p true f) k' L) := by
        intro c bl br hc0 hl hrr e
        rcases hG.2 x hx with rfl | hxi
        · exact kill bl (by rw [e]; exact kill_l p bl c hl y)
        · rcases hG.2 y hy with rfl | hyi
          · exact kill br (by rw [e]; exact kill_r p br c hrr x)
          · exact keep (e ▸ fix_bin c hc0 hxi hyi)
      rcases ht with e | e | e
      · exact main and false false rfl rfl rfl e
      · exact main or true true rfl rfl rfl e
      · exact main bDiff false true rfl rfl rfl e
theorem good_L0 {n : ℕ} (p : Fin n) : Good p (L0 n) := by
  refine ⟨List.mem_cons_self, ?_⟩
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact Or.inr ⟨fun _ => rfl, rfl⟩
  obtain ⟨q, rfl⟩ := (List.mem_ofFn' _ _).mp hg
  by_cases hq : q = p
  · exact Or.inl (by rw [hq])
  · refine Or.inr ⟨fun b => ?_, rfl⟩
    funext z
    simp [rho, upd, fV, hq]
theorem ne_F {n : ℕ} (g : BF n) (x : Fin n → Bool) (h : g x = true) : g ≠ fF n := by
  intro e; rw [e] at h; exact Bool.noConfusion h
theorem reads {n : ℕ} (p : Fin n) (g : BF n) (x : Fin n → Bool)
    (h : (rho p false g x != rho p true g x) = true) : ¬ ∀ b, rho p b g = g := by
  intro hi
  rw [hi false, hi true] at h
  simp at h
def pt {n : ℕ} (m : ℕ) : Fin n → Bool := fun i => Nat.testBit m i.val
theorem all_pts {n : ℕ} (P : (Fin n → Bool) → Prop) (h : ∀ m < 2 ^ n, P (pt m)) :
    ∀ x : Fin n → Bool, P x := by
  intro x
  have e : x = pt (Nat.ofBits x) := by
    funext i
    exact (Nat.testBit_ofBits_lt x i.val i.isLt).symm
  rw [e]
  exact h _ (Nat.ofBits_lt_two_pow x)
def nd (FULL x y : ℕ) : ℕ := Nat.land x (Nat.xor FULL y)
abbrev NCand (FULL : ℕ) (L : List ℕ) (s : ℕ) : Prop := Cand Nat.land Nat.lor (nd FULL) L s
abbrev NReach (FULL T k : ℕ) (L : List ℕ) : Prop := Reach Nat.land Nat.lor (nd FULL) T k L
abbrev NReachN (FULL T k : ℕ) (L F : List ℕ) : Prop :=
  ReachN Nat.land Nat.lor (nd FULL) T k L F
def memb (a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: l => cond (Nat.beq a b) true (memb a l)
theorem memb_iff {a : ℕ} {l : List ℕ} : memb a l = true ↔ a ∈ l := by
  induction l with
  | nil => simp [memb]
  | cons b l ih =>
    simp only [memb, List.mem_cons]
    by_cases h : a = b
    · subst h; rw [Nat.beq_refl]; simp
    · have : Nat.beq a b = false := by
        rw [← Bool.not_eq_true]; exact fun hb => h (Nat.eq_of_beq_eq_true hb)
      rw [this]; simp [ih, h]
def force (n : ℕ) (k : ℕ → Bool) : Bool :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)
theorem force_eq (n : ℕ) (k : ℕ → Bool) : force n k = k n := by
  cases n <;> rfl
def cands2 (FULL : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: l => l.flatMap (fun y => [Nat.land x y, Nat.lor x y, nd FULL x y, nd FULL y x]) ++
      cands2 FULL l
def cands (FULL : ℕ) (L : List ℕ) : List ℕ := L.map (fun x => nd FULL x x) ++ cands2 FULL L
theorem cands2_sound (FULL : ℕ) : ∀ (L : List ℕ) (s : ℕ), s ∈ cands2 FULL L →
    NCand FULL L s := by
  intro L
  induction L with
  | nil => intro s hs; exact absurd hs List.not_mem_nil
  | cons x l ih =>
    intro s hs
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨y, hy, h⟩ := List.mem_flatMap.mp h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      have hx' : x ∈ x :: l := List.mem_cons_self
      have hy' : y ∈ x :: l := List.mem_cons_of_mem _ hy
      rcases h with h | h | h | h
      · exact ⟨x, hx', y, hy', Or.inl h⟩
      · exact ⟨x, hx', y, hy', Or.inr (Or.inl h)⟩
      · exact ⟨x, hx', y, hy', Or.inr (Or.inr h)⟩
      · exact ⟨y, hy', x, hx', Or.inr (Or.inr h)⟩
    · exact (ih s h).mono _ _ _ (fun z hz => List.mem_cons_of_mem _ hz)
theorem cands2_complete (FULL : ℕ) : ∀ (L : List ℕ) (x y : ℕ), x ∈ L → y ∈ L → x ≠ y →
    Nat.land x y ∈ cands2 FULL L ∧ Nat.lor x y ∈ cands2 FULL L ∧ nd FULL x y ∈ cands2 FULL L := by
  intro L
  induction L with
  | nil => intro x y hx; exact absurd hx List.not_mem_nil
  | cons a l ih =>
    intro x y hx hy hxy
    have key : ∀ z ∈ l, Nat.land a z ∈ cands2 FULL (a :: l) ∧ Nat.lor a z ∈ cands2 FULL (a :: l)
        ∧ nd FULL a z ∈ cands2 FULL (a :: l) ∧ nd FULL z a ∈ cands2 FULL (a :: l) := by
      intro z hz
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨z, hz, by simp⟩)
    rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
    · exact absurd (hx.trans hy.symm) hxy
    · rw [hx]; exact ⟨(key y hy).1, (key y hy).2.1, (key y hy).2.2.1⟩
    · rw [hy, show Nat.land x a = Nat.land a x from Nat.and_comm x a,
        show Nat.lor x a = Nat.lor a x from Nat.or_comm x a]
      exact ⟨(key x hx).1, (key x hx).2.1, (key x hx).2.2.2⟩
    · obtain ⟨h1, h2, h3⟩ := ih x y hx hy hxy
      exact ⟨List.mem_append_right _ h1, List.mem_append_right _ h2, List.mem_append_right _ h3⟩
theorem cands_sound {FULL : ℕ} {L : List ℕ} {s : ℕ} (h : s ∈ cands FULL L) :
    NCand FULL L s := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
    exact ⟨x, hx, x, hx, Or.inr (Or.inr rfl)⟩
  · exact cands2_sound FULL L s h
theorem cands_complete {FULL : ℕ} {L : List ℕ} {s : ℕ} (h : NCand FULL L s) (hl : s ∉ L) :
    s ∈ cands FULL L := by
  obtain ⟨x, hx, y, hy, h⟩ := h
  by_cases hxy : x = y
  · subst hxy
    rcases h with h | h | h
    · have e1 : Nat.land x x = x := Nat.and_self x
      rw [e1] at h; rw [h] at hl; exact absurd hx hl
    · have e1 : Nat.lor x x = x := Nat.or_self x
      rw [e1] at h; rw [h] at hl; exact absurd hx hl
    · rw [h]; exact List.mem_append_left _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · obtain ⟨h1, h2, h3⟩ := cands2_complete FULL L x y hx hy hxy
    rcases h with h | h | h
    · rw [h]; exact List.mem_append_right _ h1
    · rw [h]; exact List.mem_append_right _ h2
    · rw [h]; exact List.mem_append_right _ h3
def loop (f : ℕ → List ℕ → Bool) (L : List ℕ) : List ℕ → List ℕ → Bool
  | [], _ => false
  | c :: cs, F =>
    force c (fun c' => cond (memb c' L) (loop f L cs F)
      (cond (memb c' F) (loop f L cs F)
        (cond (f c' F) true (loop f L cs (c' :: F)))))
theorem loop_cons (f : ℕ → List ℕ → Bool) (L : List ℕ) (c : ℕ) (cs F : List ℕ) :
    loop f L (c :: cs) F = cond (memb c L) (loop f L cs F)
      (cond (memb c F) (loop f L cs F)
        (cond (f c F) true (loop f L cs (c :: F)))) := by
  simp only [loop, force_eq]
theorem land_abs1 (x y : ℕ) : Nat.beq (Nat.land x (Nat.land x y)) (Nat.land x y) = true := by
  have e : Nat.land x (Nat.land x y) = Nat.land x y := by
    show x &&& (x &&& y) = x &&& y
    rw [← Nat.and_assoc, Nat.and_self]
  rw [e]; exact Nat.beq_refl _
theorem land_abs2 (x y : ℕ) : Nat.beq (Nat.land y (Nat.land x y)) (Nat.land x y) = true := by
  have e : Nat.land y (Nat.land x y) = Nat.land x y := by
    show y &&& (x &&& y) = x &&& y
    rw [Nat.and_comm x y, ← Nat.and_assoc, Nat.and_self]
  rw [e]; exact Nat.beq_refl _
theorem lor_abs1 (x y : ℕ) : Nat.beq (Nat.lor x (Nat.lor x y)) (Nat.lor x y) = true := by
  have e : Nat.lor x (Nat.lor x y) = Nat.lor x y := by
    show x ||| (x ||| y) = x ||| y
    rw [← Nat.or_assoc, Nat.or_self]
  rw [e]; exact Nat.beq_refl _
theorem lor_abs2 (x y : ℕ) : Nat.beq (Nat.lor y (Nat.lor x y)) (Nat.lor x y) = true := by
  have e : Nat.lor y (Nat.lor x y) = Nat.lor x y := by
    show y ||| (x ||| y) = x ||| y
    rw [Nat.or_comm x y, ← Nat.or_assoc, Nat.or_self]
  rw [e]; exact Nat.beq_refl _
theorem nd_abs (FULL x y : ℕ) : Nat.beq (Nat.land x (nd FULL x y)) (nd FULL x y) = true :=
  land_abs1 x (Nat.xor FULL y)
def candCheck (FULL T : ℕ) (L U Dn : List ℕ) : Bool :=
  U.any (fun x => U.any (fun y => Nat.beq (Nat.land x y) T) ||
      L.any (fun y => Nat.beq (nd FULL x y) T)) ||
    Dn.any (fun x => Dn.any (fun y => Nat.beq (Nat.lor x y) T))
def upOf (T : ℕ) (L : List ℕ) : List ℕ := L.filter (fun x => Nat.beq (Nat.land x T) T)
def dnOf (T : ℕ) (L : List ℕ) : List ℕ := L.filter (fun x => Nat.beq (Nat.lor x T) T)
theorem candCheck_complete {FULL T : ℕ} {L : List ℕ} (h : NCand FULL L T) :
    candCheck FULL T L (upOf T L) (dnOf T L) = true := by
  obtain ⟨x, hx, y, hy, h⟩ := h
  unfold candCheck
  rw [Bool.or_eq_true]
  rcases h with h | h | h
  · subst h
    left
    rw [List.any_eq_true]
    refine ⟨x, List.mem_filter.mpr ⟨hx, land_abs1 x y⟩, ?_⟩
    rw [Bool.or_eq_true]
    left
    rw [List.any_eq_true]
    exact ⟨y, List.mem_filter.mpr ⟨hy, land_abs2 x y⟩, Nat.beq_refl _⟩
  · subst h
    right
    rw [List.any_eq_true]
    refine ⟨x, List.mem_filter.mpr ⟨hx, lor_abs1 x y⟩, ?_⟩
    rw [List.any_eq_true]
    exact ⟨y, List.mem_filter.mpr ⟨hy, lor_abs2 x y⟩, Nat.beq_refl _⟩
  · subst h
    left
    rw [List.any_eq_true]
    refine ⟨x, List.mem_filter.mpr ⟨hx, nd_abs FULL x y⟩, ?_⟩
    rw [Bool.or_eq_true]
    right
    rw [List.any_eq_true]
    exact ⟨y, hy, Nat.beq_refl _⟩
def test2 (FULL T : ℕ) (L U Dn : List ℕ) (c : ℕ) : Bool :=
  (Nat.beq (Nat.land c T) T &&
      (U.any (fun z => Nat.beq (Nat.land c z) T) || L.any (fun z => Nat.beq (nd FULL c z) T) ||
        Nat.beq (nd FULL c c) T)) ||
    (Nat.beq (Nat.lor c T) T && Dn.any (fun z => Nat.beq (Nat.lor c z) T)) ||
    U.any (fun z => Nat.beq (nd FULL z c) T)
def check2 (FULL T : ℕ) (L : List ℕ) : Bool :=
  cond (candCheck FULL T L (upOf T L) (dnOf T L)) true
    ((cands FULL L).any (test2 FULL T L (upOf T L) (dnOf T L)))
theorem check2_complete {FULL T : ℕ} {L F : List ℕ} (hT : T ∉ L) (h : NReachN FULL T 2 L F) :
    check2 FULL T L = true := by
  rcases h with h | ⟨s, hc, _, hl, hr⟩
  · exact absurd h hT
  · have left : NCand FULL L T → check2 FULL T L = true := by
      intro h
      unfold check2
      rw [candCheck_complete h]; rfl
    have key : test2 FULL T L (upOf T L) (dnOf T L) s = true → check2 FULL T L = true := by
      intro h
      have : (cands FULL L).any (test2 FULL T L (upOf T L) (dnOf T L)) = true := by
        rw [List.any_eq_true]
        exact ⟨s, cands_complete hc hl, h⟩
      unfold check2
      rw [this]
      cases candCheck FULL T L (upOf T L) (dnOf T L) <;> rfl
    have kA : ∀ y ∈ L, T = Nat.land s y → check2 FULL T L = true := by
      intro y hy h
      apply key
      subst h
      unfold test2
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true,
        List.any_eq_true]
      exact Or.inl (Or.inl ⟨land_abs1 s y,
        Or.inl (Or.inl ⟨y, List.mem_filter.mpr ⟨hy, land_abs2 s y⟩, Nat.beq_refl _⟩)⟩)
    have kO : ∀ y ∈ L, T = Nat.lor s y → check2 FULL T L = true := by
      intro y hy h
      apply key
      subst h
      unfold test2
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true (Nat.beq (Nat.lor s _) _),
        List.any_eq_true]
      exact Or.inl (Or.inr ⟨lor_abs1 s y, y, List.mem_filter.mpr ⟨hy, lor_abs2 s y⟩,
        Nat.beq_refl _⟩)
    have kD1 : ∀ y ∈ L, T = nd FULL s y → check2 FULL T L = true := by
      intro y hy h
      apply key
      subst h
      unfold test2
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true,
        List.any_eq_true (l := L)]
      exact Or.inl (Or.inl ⟨nd_abs FULL s y, Or.inl (Or.inr ⟨y, hy, Nat.beq_refl _⟩)⟩)
    have kD2 : ∀ x ∈ L, T = nd FULL x s → check2 FULL T L = true := by
      intro x hx h
      apply key
      subst h
      unfold test2
      rw [Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨x, List.mem_filter.mpr ⟨hx, nd_abs FULL x s⟩, Nat.beq_refl _⟩
    have kD3 : T = nd FULL s s → check2 FULL T L = true := by
      intro h
      apply key
      subst h
      unfold test2
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.or_eq_true]
      exact Or.inl (Or.inl ⟨nd_abs FULL s s, Or.inr (Nat.beq_refl _)⟩)
    have hsT : T = s → check2 FULL T L = true := fun e => left (e ▸ hc)
    rcases hr with h | ⟨s2, hc2, _, _, hr2⟩
    · rcases List.mem_cons.mp h with h | h
      · exact hsT h
      · exact absurd h hT
    · have hr2' : T ∈ s2 :: s :: L := hr2
      rcases List.mem_cons.mp hr2' with h | h
      · subst h
        obtain ⟨x, hx, y, hy, hop⟩ := hc2
        have e1 : Nat.land s s = s := Nat.and_self s
        have e2 : Nat.lor s s = s := Nat.or_self s
        rcases hop with hop | hop | hop
        · rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
          · rw [hx, hy, e1] at hop; exact hsT hop
          · rw [hx] at hop; exact kA y hy hop
          · rw [hy, show Nat.land x s = Nat.land s x from Nat.and_comm x s] at hop
            exact kA x hx hop
          · exact left ⟨x, hx, y, hy, Or.inl hop⟩
        · rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
          · rw [hx, hy, e2] at hop; exact hsT hop
          · rw [hx] at hop; exact kO y hy hop
          · rw [hy, show Nat.lor x s = Nat.lor s x from Nat.or_comm x s] at hop
            exact kO x hx hop
          · exact left ⟨x, hx, y, hy, Or.inr (Or.inl hop)⟩
        · rcases List.mem_cons.mp hx with hx | hx <;> rcases List.mem_cons.mp hy with hy | hy
          · rw [hx, hy] at hop; exact kD3 hop
          · rw [hx] at hop; exact kD1 y hy hop
          · rw [hy] at hop; exact kD2 x hx hop
          · exact left ⟨x, hx, y, hy, Or.inr (Or.inr hop)⟩
      · rcases List.mem_cons.mp h with h | h
        · exact hsT h
        · exact absurd h hT
def chk (FULL T : ℕ) : ℕ → List ℕ → List ℕ → Bool
  | 0, L, _ => memb T L
  | 1, L, _ => cond (memb T L) true (candCheck FULL T L (upOf T L) (dnOf T L))
  | 2, L, _ => cond (memb T L) true (check2 FULL T L)
  | k + 3, L, F =>
    cond (memb T L) true (loop (fun c F' => chk FULL T (k + 2) (c :: L) F') L (cands FULL L) F)
theorem loop_complete {FULL T : ℕ} (L : List ℕ) (f : ℕ → List ℕ → Bool) (k : ℕ)
    (ih : ∀ c F, NReachN FULL T k (c :: L) F → f c F = true) (hT : T ∉ L) :
    ∀ (cs F : List ℕ), (∀ c ∈ cs, NCand FULL L c) →
      (∀ s, NCand FULL L s → s ∉ L → s ∉ F → s ∈ cs) →
      NReachN FULL T (k + 1) L F → loop f L cs F = true := by
  intro cs
  induction cs with
  | nil =>
    intro F _ hcpl hr
    rcases hr with h | ⟨s, hc, hf, hl, _⟩
    · exact absurd h hT
    · exact absurd (hcpl s hc hl hf) List.not_mem_nil
  | cons c cs ihc =>
    intro F hs hcpl hr
    have hs' : ∀ c ∈ cs, NCand FULL L c := fun x hx => hs x (List.mem_cons_of_mem _ hx)
    rw [loop_cons]
    have skip : c ∈ L ∨ c ∈ F → loop f L cs F = true := by
      intro hin
      refine ihc F hs' ?_ hr
      intro s hc hl hf
      rcases List.mem_cons.mp (hcpl s hc hl hf) with h | h
      · subst h
        rcases hin with h | h
        · exact absurd h hl
        · exact absurd h hf
      · exact h
    by_cases hcL : c ∈ L
    · rw [memb_iff.2 hcL]; exact skip (Or.inl hcL)
    · have hm : memb c L = false := by rw [← Bool.not_eq_true, memb_iff]; exact hcL
      rw [hm]
      by_cases hcF : c ∈ F
      · rw [memb_iff.2 hcF]; exact skip (Or.inr hcF)
      · have hm2 : memb c F = false := by rw [← Bool.not_eq_true, memb_iff]; exact hcF
        rw [hm2]
        rcases ReachN.dich Nat.land Nat.lor (nd FULL) _ _ _ (hs c List.mem_cons_self) hcL hr
          with h | ⟨k', hk, h⟩
        · have : loop f L cs (c :: F) = true := by
            refine ihc (c :: F) hs' ?_ h
            intro s hc hl hf
            rcases List.mem_cons.mp (hcpl s hc hl (fun hx => hf (List.mem_cons_of_mem _ hx)))
              with h | h
            · subst h; exact absurd List.mem_cons_self hf
            · exact h
          rw [this]; cases f c F <;> rfl
        · have hk' : k' = k := by omega
          subst hk'
          rw [ih c F h]; rfl
theorem chk_complete {FULL T : ℕ} : ∀ (k : ℕ) (L F : List ℕ),
    NReachN FULL T k L F → chk FULL T k L F = true := by
  intro k
  induction k with
  | zero => intro L F h; exact memb_iff.2 h
  | succ k ih =>
    intro L F h
    by_cases hT : T ∈ L
    · have hm : memb T L = true := memb_iff.2 hT
      rcases k with _ | _ | k <;> simp only [chk, hm, Bool.cond_true]
    · have hm : memb T L = false := by
        rw [← Bool.not_eq_true, memb_iff]; exact hT
      cases k with
      | zero =>
        simp only [chk, hm, Bool.cond_false]
        rcases h with h | ⟨s, hc, _, _, hr⟩
        · exact absurd h hT
        · rcases List.mem_cons.mp hr with h | h
          · subst h; exact candCheck_complete hc
          · exact absurd h hT
      | succ k =>
        cases k with
        | zero =>
          simp only [chk, hm, Bool.cond_false]
          exact check2_complete hT h
        | succ k =>
        simp only [chk, hm, Bool.cond_false]
        exact loop_complete L _ (k + 2) (fun c F' hr => ih (c :: L) F' hr) hT
          (cands FULL L) F (fun c hc => cands_sound hc)
          (fun s hc hl _ => cands_complete hc hl) h
def tt {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (g : BF n) : ℕ :=
  Nat.ofBits (fun j : Fin N => g (e j.val))
theorem tt_testBit {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (g : BF n) (i : ℕ) :
    (tt N e g).testBit i = (decide (i < N) && g (e i)) := by
  unfold tt
  by_cases h : i < N
  · rw [Nat.testBit_ofBits_lt _ _ h]; simp [h]
  · rw [Nat.testBit_ofBits_ge _ _ (not_lt.mp h)]; simp [h]
theorem tt_and {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (a b : BF n) :
    tt N e (fAnd a b) = Nat.land (tt N e a) (tt N e b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  show _ = (tt N e a &&& tt N e b).testBit i
  rw [Nat.testBit_and, tt_testBit, tt_testBit, tt_testBit]
  by_cases h : i < N <;> simp [h, fBin]
theorem tt_or {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (a b : BF n) :
    tt N e (fOr a b) = Nat.lor (tt N e a) (tt N e b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  show _ = (tt N e a ||| tt N e b).testBit i
  rw [Nat.testBit_or, tt_testBit, tt_testBit, tt_testBit]
  by_cases h : i < N <;> simp [h, fBin]
theorem tt_diff {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) (a b : BF n) :
    tt N e (fDiff a b) = nd (2 ^ N - 1) (tt N e a) (tt N e b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  show _ = (tt N e a &&& ((2 ^ N - 1) ^^^ tt N e b)).testBit i
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, tt_testBit, tt_testBit,
    tt_testBit]
  by_cases h : i < N <;> simp [h, fBin]
theorem tt_F {n : ℕ} (N : ℕ) (e : ℕ → Fin n → Bool) : tt N e (fF n) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [tt_testBit]
  simp [fF]
theorem leaf {n : ℕ} (N FULL : ℕ) (e : ℕ → Fin n → Bool) (g : BF n) (T k : ℕ) (Ln : List ℕ)
    (hFULL : 2 ^ N - 1 = FULL) (hT : tt N e g = T) (hL0 : 0 ∈ Ln)
    (hLv : ∀ p : Fin n, tt N e (fV p) ∈ Ln)
    (hc : chk FULL T k Ln [] = false) : ∀ j : ℕ, R g j (L0 n) → k + 1 ≤ j := by
  intro j hr
  by_contra hlt
  have hjk : j ≤ k := by omega
  have h1 := Reach.monoLe fAnd fOr fDiff hjk _ hr
  have h2 := Reach.map fAnd fOr fDiff Nat.land Nat.lor (nd FULL) (tt N e) (by
    intro x y s hs L' hx hy
    rcases hs with rfl | rfl | rfl
    · exact ⟨_, hx, _, hy, Or.inl (tt_and N e x y)⟩
    · exact ⟨_, hx, _, hy, Or.inr (Or.inl (tt_or N e x y))⟩
    · exact ⟨_, hx, _, hy, Or.inr (Or.inr (by rw [tt_diff, hFULL]))⟩) k _ h1
  rw [hT] at h2
  have h3 : NReach FULL T k Ln := by
    refine Reach.monoL _ _ _ _ _ _ ?_ h2
    intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    rcases List.mem_cons.mp hw with rfl | hw
    · rw [tt_F]; exact hL0
    obtain ⟨q, rfl⟩ := (List.mem_ofFn' _ _).mp hw
    exact hLv q
  have h4 := chk_complete k Ln [] (Reach.toN Nat.land Nat.lor (nd FULL) k Ln h3)
  rw [hc] at h4
  exact Bool.false_ne_true h4
theorem lb_size {n : ℕ} (f : BF n) (B : ℕ) (hB : ∀ k : ℕ, R (nz f) k (L0 n) → B ≤ k) :
    ∀ t : ℕ, HasCircuitSize n f t → B ≤ t := by
  rintro t ⟨C, hC, hs, he⟩
  have hok : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have := hC g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have h1 := hB _ (prog_of_gatelist f C.gates C.output hok he)
  have h2 := cnt_le C.gates
  have h3 : C.gates.length ≤ t := hs
  omega
theorem not_shape {n : ℕ} (f : BF n) (B : ℕ) (hB : ∀ k : ℕ, R (nz f) k (L0 n) → B ≤ k)
    (Wg : List Gate) (wo : ℕ)
    (hWm : ∀ g ∈ Wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWl : Wg.length ≤ B + 1)
    (hWe : ∀ x : Fin n → Bool, Circuit.eval ⟨Wg, wo⟩ (List.ofFn x) = f x)
    (gates : List Gate) (o : ℕ)
    (hok : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (he : ∀ x : Fin n → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin n → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = f x := by
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · have h1 := hB _ (prog_of_gatelist f gates o hok he)
    have h2 := cnt_lt gates hn
    exact ⟨Wg, wo, hWm, by omega, hWe⟩
  · refine ⟨gates, o, ?_, Nat.le_refl _, he⟩
    intro g hg
    obtain ⟨h1, h2⟩ := hok g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨g, hg, h⟩ hn
def monoOK (g : Gate) : Bool :=
  (match g.op with
    | GateOp.and => true
    | GateOp.or => true
    | _ => false) && decide (g.inputs.length ≤ 2)
theorem monoOK_sound (Wg : List Gate) (h : Wg.all monoOK = true) :
    ∀ g ∈ Wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  obtain ⟨op, ins⟩ := g
  unfold monoOK at h1
  rw [Bool.and_eq_true] at h1
  obtain ⟨h2, h3⟩ := h1
  refine ⟨?_, of_decide_eq_true h3⟩
  cases op <;> simp at h2 ⊢
def tblOK (c : ℕ) (F : List ℕ) : List (ℕ × List ℕ) → Bool
  | [] => false
  | e :: _ => decide (c = e.1 ∧ F = e.2)
def loopT (L : List ℕ) : List ℕ → List ℕ → List (ℕ × List ℕ) → Bool
  | [], _, _ => true
  | c :: cs, F, tbl =>
    cond (memb c L) (loopT L cs F tbl)
      (cond (memb c F) (loopT L cs F tbl)
        (cond (tblOK c F tbl) (loopT L cs (c :: F) tbl.tail) false))
def AllF (f : ℕ → List ℕ → Bool) : List (ℕ × List ℕ) → Prop
  | [] => True
  | e :: tl => f e.1 e.2 = false ∧ AllF f tl
theorem loop_false (f : ℕ → List ℕ → Bool) (L : List ℕ) : ∀ (cs F : List ℕ)
    (tbl : List (ℕ × List ℕ)), loopT L cs F tbl = true → AllF f tbl → loop f L cs F = false := by
  intro cs
  induction cs with
  | nil => intro F tbl _ _; rfl
  | cons c cs ih =>
    intro F tbl h ha
    rw [loop_cons]
    unfold loopT at h
    cases hL : memb c L
    · rw [hL] at h
      cases hF : memb c F
      · rw [hF] at h
        cases tbl with
        | nil => exact absurd h (by simp [tblOK])
        | cons e tl =>
          cases hk : tblOK c F (e :: tl)
          · rw [hk] at h; exact absurd h (by simp)
          · rw [hk] at h
            obtain ⟨h1, h2⟩ := of_decide_eq_true hk
            obtain ⟨ha1, ha2⟩ := ha
            rw [← h1, ← h2] at ha1
            simp only [Bool.cond_false, ha1]
            exact ih (c :: F) tl h ha2
      · rw [hF] at h
        simp only [Bool.cond_false, Bool.cond_true]
        exact ih F tbl h ha
    · rw [hL] at h
      simp only [Bool.cond_true]
      exact ih F tbl h ha
theorem chk_split (FULL T k : ℕ) (L F : List ℕ) (tbl : List (ℕ × List ℕ))
    (hT : memb T L = false) (hl : loopT L (cands FULL L) F tbl = true)
    (ha : AllF (fun c F' => chk FULL T (k + 2) (c :: L) F') tbl) :
    chk FULL T (k + 3) L F = false := by
  simp only [chk, hT, Bool.cond_false]
  exact loop_false _ L _ F tbl hl ha
theorem mono_shape {n : ℕ} (f : BF n) (B : ℕ) (hB : ∀ k : ℕ, R (nz f) k (L0 n) → B ≤ k)
    (Wg : List Gate) (wo : ℕ)
    (hWm : ∀ g ∈ Wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWl : Wg.length ≤ B)
    (hWe : ∀ x : Fin n → Bool, Circuit.eval ⟨Wg, wo⟩ (List.ofFn x) = f x) :
    ∀ s : ℕ, HasCircuitSize n f s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  intro s hs
  have h1 := lb_size f B hB s hs
  refine ⟨⟨Wg, wo⟩, ?_, le_trans hWl h1, hWe⟩
  intro g hg
  obtain ⟨h2, h3⟩ := hWm g hg
  refine ⟨?_, h3⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact h2
theorem mono_shape2 {n : ℕ} (f : BF n) (B : ℕ) (hB : ∀ k : ℕ, R (nz f) k (L0 n) → B ≤ k)
    (Wg : List Gate) (wo : ℕ)
    (hWm : ∀ g ∈ Wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hWl : Wg.length ≤ B + 1)
    (hWe : ∀ x : Fin n → Bool, Circuit.eval ⟨Wg, wo⟩ (List.ofFn x) = f x) :
    ∀ s : ℕ, HasCircuitSize n f s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  rintro s ⟨⟨gates, o⟩, hC, hs, he⟩
  have hok : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    have := hC g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  obtain ⟨g2, o2, hm, hl, he2⟩ := not_shape f B hB Wg wo hWm hWl hWe gates o hok he
  have hs2 : gates.length ≤ s := hs
  refine ⟨⟨g2, o2⟩, ?_, le_trans hl hs2, he2⟩
  intro g hg
  obtain ⟨h2, h3⟩ := hm g hg
  refine ⟨?_, h3⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact h2

end Logic
namespace Search
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
theorem avail_mono {d:Nat} {bank:List Nat} {w:Nat} (h : Avail false d bank w) :
    Avail true d bank w:=by
  rcases h with h | h | ⟨h,_⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · contradiction
theorem reach_up {d:Nat} {roots:List Nat} {p bank} (h:NatReach false d roots p bank) :
    NatReach true d roots p bank:=by
  induction p generalizing bank with
  | zero=>exact h
  | succ p ih =>
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=h
    have hop' : allowedB true op = true:=by
      rcases allowed_cases hop with rfl | rfl | ⟨hc,_⟩ | ⟨hc,_⟩ <;> first | decide | contradiction
    exact ⟨b,a,c,op,hop',rfl,ih hrb,avail_mono ha,avail_mono hc⟩
theorem lower_down {d:Nat} {roots:List Nat} {T L:Nat} (h : Lower true d roots T L) :
    Lower false d roots T L:=fun p bank hr ha=>h p bank (reach_up hr) (avail_mono ha)
theorem mask256_bit (i:Nat) : mask256.testBit i = decide (i < 256):=by
  rw [mask256,Nat.testBit_two_pow_sub_one]
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
theorem andD_mask (d a b:Nat) : andD d (a&&&d) (b&&&d) = andD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [andD,Nat.testBit_and]
  cases d.testBit i <;> simp
theorem orD_mask (d a b:Nat) : orD d (a&&&d) (b&&&d) = orD d a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [orD,Nat.testBit_and,Nat.testBit_or]
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
theorem lower_base {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} (h : availB u d roots T = false) :
    Lower u d roots T 1:=by
  intro p bank hr ha
  cases p with
  | zero =>
    dsimp only [NatReach] at hr; rw [hr] at ha
    have ht:=(availB_iff u d roots T).2 ha
    rw [h] at ht; contradiction
  | succ p=>omega
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
theorem lower_ess_count {u:Bool} {d T:Nat} {roots:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : isConstB d T = false)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true) :
    Lower u d roots T (singles.length - 1):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,_,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [essOK,pairOK,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hcnt:=countP_ge_sublist (fun _=>true) hs_nd hsin_mem (fun _ _=>rfl)
  simp only [List.length_map,List.countP_true] at hcnt
  have hlen:=run_len hrun
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
theorem getD_mem {xs:List Nat} {i:Nat} (hi : i < xs.length) : xs.getD i 0 ∈ xs:=by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi
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
def gvN (w:List Nat) (g : Gate):Nat :=
  match g.op with
  | .and=>g.inputs.foldr (fun i acc=>andD mask256 (w.getD i 0) acc) mask256
  | .or =>g.inputs.foldr (fun i acc=>orD mask256 (w.getD i 0) acc) 0
  | .not=>match g.inputs with | []=>mask256 | i :: _=>negD mask256 (w.getD i 0)
  | _=>0
def execN (gs:List Gate) (w:List Nat):List Nat :=
  gs.foldl (fun l g=>l ++ [gvN l g]) w
theorem gvN_bit (w:List Nat) (g : Gate) (r:Nat) (hr : r < 256)
    (hop : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (gvN w g).testBit r = g.op.eval (g.inputs.map fun i=>(w.map (·.testBit r)).getD i false):=by
  have hm : mask256.testBit r = true:=by simp [mask256_bit,hr]
  have hgd : ∀ i,(w.map (·.testBit r)).getD i false = (w.getD i 0).testBit r:=by
    intro i; simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases w[i]? with | none=>simp | some v=>rfl
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp only [gvN,GateOp.eval,h]
    induction g.inputs with
    | nil=>simp [hm]
    | cons i l ih =>
      rw [List.foldr_cons,List.map_cons,List.all_cons,id_eq,andD,Nat.testBit_and,Nat.testBit_and,hm,Bool.and_true,hgd,ih]
  · simp only [gvN,GateOp.eval,h]
    induction g.inputs with
    | nil=>simp
    | cons i l ih =>
      rw [List.foldr_cons,List.map_cons,List.any_cons,id_eq,orD,Nat.testBit_and,Nat.testBit_or,hm,Bool.and_true,hgd,ih]
  · simp only [gvN,GateOp.eval,h]
    cases g.inputs with
    | nil=>simp [hm]
    | cons i l=>simp only [List.map_cons,List.headD_cons,negD,Nat.testBit_and,Nat.testBit_xor,hm,Bool.and_true,Bool.xor_true,hgd]
theorem execN_bit (gs:List Gate) (w:List Nat) (r:Nat) (hr : r < 256)
    (hfan : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execN gs w).map (·.testBit r) =
      gs.foldl (fun l g=>l ++ [g.op.eval (g.inputs.map fun i=>l.getD i false)]) (w.map (·.testBit r)):=by
  induction gs generalizing w with
  | nil=>rfl
  | cons g gs ih =>
    simp only [execN,List.foldl_cons] at ih ⊢
    rw [ih _ (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg'))]
    simp [gvN_bit w g r hr (hfan g List.mem_cons_self)]
def isNotGate (g : Gate):Bool:=match g.op with | .not=>true | _=>false
theorem execN_reach (u:Bool) (gs:List Gate) (roots:List Nat)
    (hfan : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hmono : u = false → ∀ g ∈ gs,isNotGate g = false) :
    ∀ (p:Nat) (w bank:List Nat),NatReach u mask256 roots p bank →
      (∀ v ∈ w,Avail u mask256 bank v) →
      ∃ p' bank',p' ≤ p + gs.countP (fun g=>!isNotGate g) ∧ NatReach u mask256 roots p' bank' ∧
        ∀ v ∈ execN gs w,Avail u mask256 bank' v:=by
  have hm256 : mask256&&&mask256 = mask256:=Nat.and_self _
  induction gs with
  | nil=>intro p w bank hr hsup; exact ⟨p,bank,by simp,hr,hsup⟩
  | cons g gs ih =>
    intro p w bank hr hsup
    have hav_gd : ∀ i,Avail u mask256 bank (w.getD i 0):=by
      intro i; by_cases hi : i < w.length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hstep : ∃ p1 bank1,p1 ≤ p + (if !isNotGate g then 1 else 0) ∧ NatReach u mask256 roots p1 bank1 ∧
        (∀ v ∈ w ++ [gvN w g],Avail u mask256 bank1 v):=by
      have hg:=hfan g List.mem_cons_self
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
      obtain ⟨hop,hlen⟩:=hg
      have hand_m : ∀ a,andD mask256 a mask256&&&mask256 = a&&&mask256:=fun a=>by
        simp [andD,Nat.and_assoc,Nat.and_self]
      have hor_0 : ∀ a,orD mask256 a 0&&&mask256 = a&&&mask256:=fun a=>by
        simp [orD,Nat.and_assoc,Nat.and_self]
      have lift_w : ∀ z,(∀ v ∈ w,Avail u mask256 (z :: bank) v):=fun z v hv=>avail_cons z v (hsup v hv)
      rcases hop with h | h | h
      · have hn : (!isNotGate g) = true:=by simp [isNotGate,h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,l⟩⟩⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN,h,hgi]))⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
              exact avail_of_eq (hand_m _).symm (hav_gd i)⟩
        · refine ⟨p + 1,opD mask256 0 (w.getD i 0) (w.getD j 0) :: bank,le_rfl,
            ⟨bank,_,_,0,by simp [allowedB],rfl,hr,hav_gd i,hav_gd j⟩,fun v hv=>?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
            exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by simp [opD,andD,Nat.and_assoc,Nat.and_self]⟩)
        · rw [hgi] at hlen; simp at hlen
      · have hn : (!isNotGate g) = true:=by simp [isNotGate,h]
        rw [hn]; simp only [ite_true]
        rcases hgi : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,l⟩⟩⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inl (by simp [gvN,h,hgi]))⟩
        · exact ⟨p,bank,by omega,hr,fun v hv=>by
            rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
            · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
              exact avail_of_eq (hor_0 _).symm (hav_gd i)⟩
        · refine ⟨p + 1,opD mask256 1 (w.getD i 0) (w.getD j 0) :: bank,le_rfl,
            ⟨bank,_,_,1,by simp [allowedB],rfl,hr,hav_gd i,hav_gd j⟩,fun v hv=>?_⟩
          rcases List.mem_append.1 hv with hv | hv; · exact lift_w _ v hv
          · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi,List.foldr_cons,List.foldr_nil]
            exact Or.inr (Or.inl ⟨_,List.mem_cons_self,by apply Nat.eq_of_testBit_eq; intro r; simp [opD,orD]; cases mask256.testBit r <;> simp⟩)
        · rw [hgi] at hlen; simp at hlen
      · cases u with
        | false =>
          have hbad:=hmono rfl g List.mem_cons_self
          simp [isNotGate,h] at hbad
        | true =>
          have hn : (!isNotGate g) = false:=by simp [isNotGate,h]
          rw [hn]; simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
          rcases hgi : g.inputs with _ | ⟨i,l⟩
          · exact ⟨p,bank,le_rfl,hr,fun v hv=>by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; exact Or.inl (Or.inr (by simp [gvN,h,hgi]))⟩
          · exact ⟨p,bank,le_rfl,hr,fun v hv=>by
              rcases List.mem_append.1 hv with hv | hv; · exact hsup v hv
              · rw [List.mem_singleton.1 hv]; simp only [gvN,h,hgi]
                exact avail_neg hm256 (hav_gd i)⟩
    obtain ⟨p1,bank1,hp1,hr1,hsup1⟩:=hstep
    obtain ⟨p2,bank2,hp2,hr2,hsup2⟩:=ih (fun g' hg'=>hfan g' (List.mem_cons_of_mem _ hg'))
      (fun hu g' hg'=>hmono hu g' (List.mem_cons_of_mem _ hg')) p1 _ bank1 hr1 hsup1
    rw [List.countP_cons]
    cases hb : !isNotGate g <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] at hp1 ⊢ <;>
      exact ⟨p2,bank2,by omega,hr2,hsup2⟩
def xs256:List Nat :=
  [(OfNat.ofNat (packedNat [0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa])),
   (OfNat.ofNat (packedNat [0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc])),
   (OfNat.ofNat (packedNat [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0])),
   (OfNat.ofNat (packedNat [0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00])),
   (OfNat.ofNat (packedNat [0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000])),
   (OfNat.ofNat (packedNat [0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000])),
   (OfNat.ofNat (packedNat [0xffffffffffffffff,0x0,0xffffffffffffffff,0x0])),
   (OfNat.ofNat (packedNat [0xffffffffffffffff,0xffffffffffffffff,0x0,0x0]))]
def pt8 (r:Nat) : Fin 8 → Bool:=fun i=>r.testBit i.val
theorem xs256_bits : ∀ r : Fin 256,xs256.map (·.testBit r.val) = List.ofFn (pt8 r.val):=by
  decide +kernel
theorem countP_not_lt {gs:List Gate} {g : Gate} (hg : g ∈ gs) (hn : isNotGate g = true) :
    gs.countP (fun x=>!isNotGate x) + 1 ≤ gs.length:=by
  induction gs with
  | nil=>simp at hg
  | cons x xs ih =>
    rw [List.countP_cons,List.length_cons]
    rcases List.mem_cons.1 hg with rfl | hxs
    · simp only [hn,Bool.not_true,Bool.false_eq_true,ite_false]
      have:=List.countP_le_length (p:=fun y=>!isNotGate y) (l:=xs); omega
    · have:=ih hxs; cases hb : !isNotGate x <;> simp only [hb,ite_true,Bool.false_eq_true,ite_false] <;> omega
theorem directSplit_to_circuit (f : (Fin 8 → Bool) → Bool) (T lb:Nat)
    (hT : ∀ r : Fin 256,T.testBit r.val = f (pt8 r.val))
    (hS : Lower true mask256 xs256 T (lb - 1))
    (hM : Lower false mask256 xs256 T lb) :
    ∀ t : ℕ,HasCircuitSize 8 f t → lb ≤ t:=by
  rintro t ⟨C,hfan,hsz,hev⟩
  have hout : (execN C.gates xs256).getD C.output 0&&&mask256 = T&&&mask256:=by
    apply Nat.eq_of_testBit_eq; intro r
    rw [Nat.testBit_and,Nat.testBit_and,mask256_bit]
    by_cases hlt : r < 256
    · simp only [hlt,decide_true,Bool.and_true]
      have h1:=execN_bit C.gates xs256 r hlt (fun g hg=>(hfan g hg).1)
      have h2:=congrArg (fun l=>l.getD C.output false) h1
      rw [xs256_bits ⟨r,hlt⟩] at h2
      have hgd : ((execN C.gates xs256).map (·.testBit r)).getD C.output false =
          ((execN C.gates xs256).getD C.output 0).testBit r:=by
        simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
        cases (execN C.gates xs256)[C.output]? with | none=>simp | some v=>rfl
      rw [hgd] at h2
      have h3 : (C.wires (List.ofFn (pt8 r))).getD C.output false = f (pt8 r):=hev (pt8 r)
      exact h2.trans (h3.trans (hT ⟨r,hlt⟩).symm)
    · simp [hlt]
  by_cases hhas : ∃ g ∈ C.gates,isNotGate g = true
  · obtain ⟨g,hg,hgn⟩:=hhas
    have hsup0 : ∀ v ∈ xs256,Avail true mask256 xs256 v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
    obtain ⟨p,bank,hp,hr,hsup⟩:=execN_reach true C.gates xs256 hfan (fun h=>Bool.noConfusion h) 0 xs256 xs256 rfl hsup0
    have hav_out : Avail true mask256 bank ((execN C.gates xs256).getD C.output 0):=by
      by_cases hi : C.output < (execN C.gates xs256).length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hL:=hS p bank hr (avail_of_eq hout hav_out)
    have hlt:=countP_not_lt hg hgn
    have : C.gates.length ≤ t:=hsz
    omega
  · push_neg at hhas
    have hmono : ∀ g ∈ C.gates,isNotGate g = false:=fun g hg=>Bool.eq_false_iff.2 (hhas g hg)
    have hsup0 : ∀ v ∈ xs256,Avail false mask256 xs256 v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
    obtain ⟨p,bank,hp,hr,hsup⟩:=execN_reach false C.gates xs256 hfan (fun _=>hmono) 0 xs256 xs256 rfl hsup0
    have hav_out : Avail false mask256 bank ((execN C.gates xs256).getD C.output 0):=by
      by_cases hi : C.output < (execN C.gates xs256).length
      · exact hsup _ (getD_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl (Or.inl (by simp))
    have hL:=hM p bank hr (avail_of_eq hout hav_out)
    have hle:=List.countP_le_length (p:=fun y=>!isNotGate y) (l:=C.gates)
    have : C.gates.length ≤ t:=hsz
    omega

end Search

namespace Case0
open Search PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def dom_7:=0xff
def roots_7:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0]
def dom_11:=0xf0f
def roots_11:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0]
def dom_15:=0xffff
def roots_15:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_19:=0xf000f
def roots_19:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 4 0]
def dom_23:=0xff00ff
def roots_23:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_27:=0xf0f0f0f
def roots_27:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_29:=0x33333333
def roots_29:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_30:=0x55555555
def roots_30:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_31:=0xffffffff
def roots_31:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_63:=0xffffffffffffffff
def roots_63:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def goal_7_32:=0xe8
def goal_11_32:=0xe08
def goal_15_32:=0xeee8
def goal_19_32:=0xe0008
def goal_23_32:=0xee00e8
def goal_27_32:=0xe0e0e08
def goal_29_0:=0x32222220
def goal_29_32:=0x32222220
def goal_30_32:=0x54444440
def goal_31_32:=0xfeeeeee8
def goal_63_0:=0xfeeeeee8feeaeee0
namespace S_29_0
def pairsG:List (Nat × Nat):=[(1,5),(1,9),(1,17),(4,5),(8,9),(12,13),(12,28),(16,17),(20,21),(20,28),(24,25),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_29.map (· &&& dom_29)
def goalM:Nat:=goal_29_0 &&& dom_29
def NN:Nat → Nat
|2=>2
|3=>11
|4=>8
|5=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x83148db1045eb9c4
|3,0=>(OfNat.ofNat (packedNat [0xe8a74740,0x865805664ce5c9db,0x4658d5063537a6e5,0x20703c3a1ca9f09d,0x1aa2ff7f159ce3aa,0x1352da780a3445e4]))
|4,0=>(OfNat.ofNat (packedNat [0x8658056674bc4026,0x43d60cad3109826f,0x2e4aa4b60e367e88,0xd12eb640a23838c]))
|5,0=>0x86580566
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat (packedNat [0xccc,0xcc0c303000000000,0x888a200220044440,0x33223322ccc0cc,0xc3000300000cc008,0xb030202044004400,0x220022cccc00c10,0x103030c000c0c333,0x3222288880000303,0xc0c33332,0x20c0c0c0c222222,0x220cc00cc3333000,0xcc00cc012121212]))
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x2094,0x8209499104a4104b,0x82082525c41292c2,0x9495104a438a812,0x9053910412904524,0x441810457b9a1290,0x4123041591412a42,0x441cc12904418820]))
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x19803
|3,0=>(OfNat.ofNat (packedNat [0xb9152264448790,0xd216424839052064]))
|4,0=>(OfNat.ofNat (packedNat [0xaa9416,0x5ac6582af15bab25]))
|5,0=>0x594
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 26 then fld (dictB (i / 512) (i / 32 % 16)) 30 (i % 32) else 0
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
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 12 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 31),wireSAt ((code >>> 7) &&& 31))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_29 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_29 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8)],[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)],[((OfNat.ofNat (packedNat [0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0])),12)],[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0])),12)],[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_29==dom_29) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_29 goalM v ys):RunD true dom_29 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 2 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 11 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 11 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 8 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 1 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 5):∀ i < NN s,bar true dom_29 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_29 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 5) (h:RunD true dom_29 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_29 roots_29 goal_29_0 6:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_29_0
theorem lowS_29_0:Lower true dom_29 roots_29 goal_29_0 6:=S_29_0.noCircuit
def isoMv_29_32:List (Nat × Nat):=[]
theorem lowS_29_32:Lower true dom_29 roots_29 goal_29_32 6:=lower_iso isoMv_29_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_0
namespace S_7_32
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(2,3),(2,6),(4,5),(4,6)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3f
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_7.map (· &&& dom_7)
def goalM:Nat:=goal_7_32 &&& dom_7
def NN:Nat → Nat
|2=>1
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xd4bda944
|3,0=>0xd4bda944
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xf0ccaa
|_,_=>0
def stPool:Nat → Nat
|0=>0x924
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 8 (i % 32) else 0
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
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 6 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 3),wireSAt ((code >>> 4) &&& 3))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_7 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_7 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2)],[((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)],[((OfNat.ofNat (packedNat [0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a])),3)],[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2),((OfNat.ofNat (packedNat [0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a])),3)],[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2),((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_7==dom_7) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_7 goalM v ys):RunD true dom_7 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_7 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 1 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_7 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_7 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_7 goalM s xsM):False:=by
  have hmin:2 ≤ s:=by have hl:=run_len h;change 3 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_7 roots_7 goal_7_32 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_7_32
theorem lowS_7_32:Lower true dom_7 roots_7 goal_7_32 4:=S_7_32.noCircuit
def isoMv_19_32:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)]
theorem lowS_19_32:Lower true dom_19 roots_19 goal_19_32 4:=lower_iso isoMv_19_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_32
def isoMv_30_32:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)]
theorem lowS_30_32:Lower true dom_30 roots_30 goal_30_32 6:=lower_iso isoMv_30_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_29_0
def isoMv_11_32:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)]
theorem lowS_11_32:Lower true dom_11 roots_11 goal_11_32 4:=lower_iso isoMv_11_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_32
theorem lowS_15_32:Lower true dom_15 roots_15 goal_15_32 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xf0f0,1,5)] (by decide +kernel) (by decide +kernel) lowS_11_32
def isoMv_27_32:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0])),12)]
theorem lowS_27_32:Lower true dom_27 roots_27 goal_27_32 5:=lower_iso isoMv_27_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
def isoMv_23_32:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8)]
theorem lowS_23_32:Lower true dom_23 roots_23 goal_23_32 5:=lower_iso isoMv_23_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_32
namespace S_31_32
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(1,9),(1,17),(2,3),(2,6),(2,10),(2,18),(4,5),(4,6),(8,9),(8,10),(12,13),(12,14),(12,28),(16,17),(16,18),(20,21),(20,22),(20,28),(24,25),(24,26),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x7fffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_31.map (· &&& dom_31)
def goalM:Nat:=goal_31_32 &&& dom_31
def NN:Nat → Nat
|2=>7
|3=>77
|4=>153
|5=>235
|6=>70
|7=>9
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>(OfNat.ofNat (packedNat [0x53a85667,0x4fc033df3f5c7174,0x300689a01c45d31a,0x14d70c5d03a150a5]))
|3,0=>(OfNat.ofNat (packedNat [0x90d1dfab,0x8990f69b7550d4cf,0x6c27ed326ad4e26f,0x687ea07466a4a201,0x6485eb3b5f115b95,0x59a823b5580ade97,0x57d13d2c54ef1fcd,0x54e018925492e55d,0x51e88ee04fd0f70f,0x4eb3003f46adbe74,0x4669e3ce43f88d71,0x43f161e63e214179,0x3e03051b3c2dc9d8,0x3a98596f36dc9f29,0x34cc583834bb2483,0x2d88e36a2cf84f96,0x2c27310429ce8804,0x27770a5426ed54d5,0x258e37d52530e167,0x23bc204423466522,0x231d07d52236d838,0x2185747e1ed7e9c7,0x1d94767f1d1f4d5b,0x19d0a71018859ea7,0x169e8a92167df7c9,0x1640cb1f162e3dfa,0x15ca8b371432d879,0x1398d167130d49ad,0x11d3f69911985e74,0x105f55731036b4f8,0xf99f16d0f122e68,0xf08ea810f04c661,0xe99da4d0d26bab3,0xc18d3fc0aef656e,0x9f54dd609367e18,0x709043d058262a7,0x550edfb04e9f8c7,0x20dde5201e7a253,0x14ecf35009331b2]))
|4,0=>(OfNat.ofNat (packedNat [0x417116b14111b6ca,0x403943e73f577948,0x3e9d7ea43e74c82e,0x3c3152cd3bab2226,0x3b7223f73b64c5eb,0x3ae364283acec343,0x3aa6da43392d2596,0x3612eb463610e05d,0x34e563ce34df5f8b,0x344f881e33a4ec4e,0x33954b5a337fa951,0x337d731c33119725,0x330866f931b97460,0x2fece2e22e29117d,0x2d42133f2b554e26,0x2a762288291d942f,0x28ac9fee288e39c8,0x27e7812e25ef984c,0x2597348f24d241e0,0x23a162b42301b654,0x22e77f7422276a1e,0x2202a83f21dec1e9,0x21d9df3d21bd1f10,0x218d36b120522a48,0x1fed43491f87dcae,0x1eeae2421e12d587,0x1e0d96ef1d975c5c,0x1d96002f1d913ce9,0x1c6661981c23c53c,0x1bf44b9b1b40d457,0x1af13ced1ac52f87,0x1aa8bce31a408d24,0x1a1de5d518ffead0,0x1808b88017981dfe,0x174af65717273acf,0x170094d3170044ca,0x161826c715ce67fc,0x1572a7d615312f4d,0x1519cabf14779299,0x13beb97213b9c819,0x12a1dbc511977d28,0x110eb67b10b55d7c,0x1057524d0fdad279,0xf62f8d50f2fbc53,0xedac97f0eb820b1,0xe5a37fa0ded2e23,0xda9eaf90c39d32b,0xc1c7d880bbf7884,0xb0803980abb799d,0x9c38b2009548af9,0x93d1a6708d80154,0x8c6b48c089a4300,0x8409c3508404deb,0x835b913081c4455,0x814ddb50772805a,0x6d064e806cd007a,0x5ac74cf05a7da57,0x5a4e2df052c73b2,0x51e3347050e3e9c,0x4a3aa0f0466f7b3,0x45051b303fb1338,0x2dd8e9a02a367b9,0x1e0b4050117afc3,0x778aa300652a94]))
|4,1=>(OfNat.ofNat (packedNat [0xb4762afd,0xaff2ec2eac90b138,0x9614f7c49514aad2,0x92e964ed8eb8a319,0x89019e80818f0850,0x7f6dd25e7522687e,0x74c145256edf4c7f,0x6a1cce1f686c08cd,0x656fcc035dab739f,0x596b636c5889f44a,0x4fc7bf944d6566ce,0x4bd64c55474361b5,0x4572d46341e662fb]))
|5,0=>(OfNat.ofNat (packedNat [0x1f78c0bb1f710856,0x1f1cfbd21ecf0f80,0x1dedd7871dc83cfa,0x1da9ab4e1d1e9bca,0x1c919a4c1c77b5a0,0x1c6866fd1c4e1fac,0x1bb691161b4479a0,0x1afefac519dd3354,0x19927a8f198ce1f3,0x190b5d3b1855f9d3,0x17f89e0017b0a43a,0x17a8e1701792c8a7,0x1752c815172ed2cf,0x172bdf4117273acf,0x170044ca16b77f9b,0x1627544f16138e74,0x15f4f6f015ad7704,0x157282eb149dce49,0x1492d12714878698,0x144a2dda13d99da6,0x13b0ee6e12e256e8,0x12673055125ab8bb,0x11ec379b11d035ac,0x11c48365118951c4,0x116c7f2a115af43c,0x1123d3a61050a710,0x1041032310028944,0xf9e51030f9b9965,0xf7afd400f3e8149,0xee631fc0eaea806,0xe9b53410e1ec4c7,0xdf86a1c0d7cdf9a,0xd6f08870cb79559,0xc2eb2090c287cef,0xc19c63b0c173e4c,0xb0e103c0ad15a45,0xa4954ce0a09a330,0x9f7608009d91913,0x9b7f91f09a7d8f7,0x976a6d00944797a,0x904989008de7bf2,0x89caaa2087b1dd7,0x8701565085a2f7e,0x7f0828e07c0faa8,0x733b4020726a3c3,0x71722e2070556e0,0x6dcae4206d064e8,0x6c052ef06ac28f2,0x698ad3f06759934,0x6687d6d065e2909,0x60de89705a7cb26,0x5a1a993056afecc,0x54408c7053466f8,0x51c01440517f4bd,0x42f0bce03bfdaad,0x39aaf3f03810e8c,0x370aea602fb6753,0x2e31f0e02a0479c,0x29aafff027d3ea5,0x26521b7022e0152,0x1d6939901963a33,0x15d58120145c582,0x135fc7a00fcb713,0xbc555a00487229]))
|5,1=>(OfNat.ofNat (packedNat [0xb3ebbbb7,0x9e0ec00589c58539,0x7e0e41b17d6d1c65,0x71a1abf3710c4566,0x70d611ff6fb648e8,0x6a75fe2263b605c6,0x638b72ac62943e55,0x60f470056059d012,0x5fabf0a55f25078f,0x5c2226c25b7132d6,0x5a1964a056b9bb40,0x53b9c923520615d7,0x51790c815155ba41,0x50cf838b4dc7e76c,0x4d840cc64aca5959,0x4aa1c6924a822318,0x4a1feaf949df6f92,0x48532aec4633d28f,0x42973adb41870255,0x41206af340b2036a,0x3ee26ebd3e7cf6c6,0x3e75b9c93dd1a568,0x3da0d34f3d4119e4,0x3d3f4bc73d0cba1c,0x3b7560c23ada78ab,0x3a9736fe3949d807,0x38e89bda3846c0e2,0x37934907377b388b,0x362c6c3635b5e6c5,0x35929ab034a30c62,0x344e843d33ccea18,0x3349baee324af455,0x32324c2131faa9a7,0x314295dc30b117c6,0x3092493b30749df8,0x2f3520cf2eb642ba,0x2e73afda2e6a8a59,0x2e176abf2da5b619,0x2d7170af2d575897,0x2ce69fc12c046261,0x2bf9d69a2bde9fb5,0x2a7c26da290f0418,0x28c79243289f9d76,0x2806214e27b8c470,0x25694e7d255673e4,0x255288b024fe9f80,0x24f1e17b24dcb664,0x24ab7caf245ac8f3,0x241448e02352f7c2,0x2311a020220ce313,0x2203710d2197c44a,0x210ae4e520969c35,0x200d758c20084a33,0x1fe97d201fcff3db]))
|6,0=>(OfNat.ofNat (packedNat [0x95d2cc119515d9ac,0x925b8bc48cc90b26,0x680ad10c5f84236f,0x5f4048c95cc01e27,0x5aa3dacd53b9c923,0x5226a46650ad6cda,0x4dd461924c7b5149,0x44e04f8d431deb01,0x41fd8d203f1826db,0x3c811b283abf1546,0x3a5bd97936ace453,0x3471b2f2341309da,0x33c935fc31c1c236,0x3161aefe30b117c6,0x2f3da2442eb642ba,0x2c5545952bf9d69a,0x28c7924328b4b7a6,0x289999ce2806214e,0x2726249d25bdec56,0x2311a02022fed1a0,0x21b4f2fa1fbd27c9,0x1f7108561b035802,0x1b017318197bee94,0x18d417f81843313c,0x17f89e0017f3b30d,0x17232ed71649e54b,0x162c983815af50bf,0x114131721058cbbe,0xf837eb50f7afd40,0xe61fd7609a0ff5b,0x8f6698f089d02fa,0x8088c3706c052ef,0x5f43a9b0550d33f,0x42f0bce02d98d73,0x17e3b29017db7bb]))
|7,0=>(OfNat.ofNat (packedNat [0x569c8b90,0x2c56ab27258c480e,0x205f4d0c1f16380d,0x1495c9760d59fc0a,0x9e2bbbd090d6eb4]))
|8,0=>0x1f16380d
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat (packedNat [0xffffaa88ffccffcc,0xfe00fe88888888,0x11ee11eeffffcccc,0xffeeff00fefef0f0,0xaaaaaaaacc88cc88,0x55ee55eef8fff8f8,0x10f010f0cccccccc,0x5555aaaa0f0f0e0e,0xffff8888ffe0ffe0,0xffff000011661166,0xf0ff0f08f8ff8f8,0xeeaaeeaa0033ffcc,0xff88ff881111eeee,0xff00ff00eeeeeeee,0xf0ff8f8f0f0f0f0,0x6666666600ffff00]))
|0,1=>(OfNat.ofNat (packedNat [0xe8e8e8e857005700,0x3c3c3c3c11441144,0x220022fefe0000,0xfcfcf8f833cc33cc,0xf000f0f0e0e0e0e0,0x76767676aa88aa88,0x33ee33eeffffaaaa,0xeeeeeeccffe8ffe8,0xaa00aa000055ffaa,0xfffff0f0f0f00000,0xff880f08ff0f0000,0xf8f8f8f8f8e8f8e8,0xf8ff888888ff8888,0xff00f0f0e0e0,0xffffa8a8fcfcfcfc,0xeaeaeaea0000ffee]))
|0,2=>(OfNat.ofNat (packedNat [0xf000f088ffff88,0x4444444422222222,0xeeeeeeeacc00cc00,0x55665566ffeeee00,0xfcfca8a8ffffff00,0xff888888ffffcc88,0x11ff0000ff0fff00,0xc0c0c0c056565656,0xf0f00e0e11110000,0xeeeefafafafa,0xeee0eee0f0faf0fa,0xfc00fc00ff0000,0x99ff8888ffaaffaa,0xeecceecc0f0e0f0e,0xffff00f0ffffee00,0x11cc11ccfefefefe]))
|0,3=>(OfNat.ofNat (packedNat [0x555544443333cccc,0xff00ee00f0fff0f0,0xa4a4a4a432323232,0xffffff88ff000000,0xf800f8ffa8ffa8,0xffeeffeeee00ee00,0xff00ffaa0000ffcc,0x1100110000660066,0xffff0a0a0f0f0c0c,0xeeeeeeec98989898,0xe0e0e0eaaaa4444,0x33332222bebebebe,0xa8a8a8a8ff000f00,0x7676ecececec,0x37370000fff0fff0,0xf000f0000f000f00]))
|0,4=>(OfNat.ofNat (packedNat [0xffffe0e0ffc8ffc8,0xfafac8c8ccccaaaa,0xf0f0fff000ff00cc,0xcecececec2c2c2c2,0x55aa55aa00440044,0xafafaeae0a0a0a0a,0x77667766eeeeaaaa,0xcfcacfca1a1a1a1a,0xf0ff000000aa00aa,0xffc0ffc00f0a0f0a,0xff0eff0effccaaaa,0xffff0f0000ff00aa,0x111144440f0f0000,0xcfcfcccc10101010,0xff0aff0a0f0c0f0c,0xff00fff0faaafaaa]))
|0,5=>(OfNat.ofNat (packedNat [0xcc00cc0000aaaa,0xfffe0000fcfc,0xaafaaafaaaaa0000,0x3030707088f888f8,0xccccccc0fff8fff8,0xfffffcfc0000f0f0,0x1100ff00fffafffa,0xffee0000f0f000f0,0xfefe0e0e55445544,0xee88ee88ffff88f8,0x1f1f0000eeee0000,0xffaaff88ffafff00,0xff00ff500f0f0a0a,0xa0a0a0a0fef0fef0,0xaaaafafaff0cff0c,0xcccccc8800ee00ee]))
|0,6=>(OfNat.ofNat (packedNat [0x33330000ffff5500,0xff00ffeefffffafa,0xffaaaaaafc00fc00,0xff0eaaaaaaa0,0xfcccfccc00ff00ee,0xfeee1e1e1e1e,0x8f8f888811aa11aa,0xff888f8854545454,0xfeeefeee33663366,0x54445444ffffeeee,0x4444ffcccccc,0xccccfcfc00ff33cc,0x1c1c1c1c55555554,0xe0e00ff55aa,0xff22ff22ff03ff00,0xeeeecccc0000cccc]))
|0,7=>(OfNat.ofNat (packedNat [0x5454f000ff00,0xf5f5f0f0fffffff0,0xff00fffc0000ffaa,0xa0a0aaaafafaaaaa,0xccffcccc3300ff00,0xfffefffe30303030,0xfa00fabbbbaaaa,0x3f3f0000cccc0000,0xffeeffaa22322232,0xffff332233ff22aa,0xcfcf8a8a05050000,0xfafa1010f0f0,0xaaaaffaaff00aa00,0xc0c0c0c03000300,0xffff00aac8c8c8c8,0xffffffaaffff0050]))
|0,8=>(OfNat.ofNat (packedNat [0xcccc888855555454,0x5050505003030202,0xfffffffa55555550,0xf0c55005500,0xffccff88fcfc0c0c,0xaaffaaaaddccddcc,0x4040404fbfafbfa,0xffff0500ffffbbaa,0x8888ff88ddddcccc,0x33333232cf00cf00,0xff11ff00fac8fac8,0x4444f4f4cccceeee,0xaaaacccc33223322,0xffffffcc00ff00fc,0xaaaa8888ffffcc00,0xcfcccfccee00eeee]))
|0,9=>(OfNat.ofNat (packedNat [0xff00cc00afafaaaa,0x555500000f0f0f0a,0xefeeefeef0e0f0e0,0xeeeeee03030000,0x5000500fa0afa0a,0xaafeaafeccaaccaa]))
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x105c700d028dc02,0xd028d86a0d03810,0x260d010d06632028,0x8620d1800808020,0x90bc5c2d038b0080,0xd15808082a028a40,0x80d028a008051380,0x80802020984a0f02,0x8900823028884207,0x1010401f0f00812,0xd02860020f01010,0x3a0d01070361a0c8,0x602e0d010582a0d0,0x2850080f02810260,0x509044200f070080,0x80d010300e040581,0x4080a01024100701,0x180a04018080200]))
|1=>(OfNat.ofNat (packedNat [0x31184020d00980be,0x20905cbc052e970,0x160d02888b60d011,0x68b258010482e2d0,0x295c08562a808085,0x40280808290905c0,0x501004a60d290a,0x4080d02944a00d02,0x80488420f0081205,0x278482e07011389a,0xd0f130960d25010,0x9229021204a05010,0x108e0d2311488430,0x2808020d03890084,0x20105c820d029007,0xe0d0b8f87a0f0c80,0x8080d010f0760e1d,0x482e0d028e4081f]))
|2=>(OfNat.ofNat (packedNat [0xd01404174388c0a,0x22010101e0501011,0xc32028080885068,0x1c0404420340a221,0x9241a830905d040,0xd408882e5d069890,0x40901404173f9f,0x81a7d0905c200f02,0x9f0080d029ecf479,0x3c008080d02180ee,0xd3b05c7a0f3a808,0xe87301010e40d011,0xc4e00502070166f0,0x2810dc051d008023,0x202808da0d029b0d,0x605011a8d20d029a,0xce0f33008080501,0x10ca0526190c60d]))
|3=>(OfNat.ofNat (packedNat [0x4e8482e320286024,0x1706814805133808,0x81c240943405012,0x702e0d4d8482e9a0,0x10102417000340a0,0x2021c01a054c85cd,0xc0d0288930170681,0x480360e03404124b,0xa581a4c0105c700d,0x28492a940681404,0x449868640501248,0x1a05488482e0d029,0x30249002a3c24173,0x58340a22260101a8,0xd0905d180d458482,0xe604501404120ba2,0x404120ba201a020b,0x8e0e40d0f1180445]))
|4=>(OfNat.ofNat (packedNat [0x92b00a020905cac,0x320f0080805110d8,0x2eab0d01404aa0b8,0x340a02021b01a050,0x905c200d03808088,0x60694804040e0355,0x2020905c1a050100,0x4be0d0285cce3d19,0x1404044d0695002,0x905c1aa70905d4c,0xd4f13024a506a90,0x2417240340a22022,0x8c641901010240d2,0x328804040f014041,0x2088680a025085c1,0xa0501005409f0290,0x2417078146e120b,0x8353c4c010105a05]))
|5=>(OfNat.ofNat (packedNat [0x104976a02b0340a,0x29020c80a125d2e4,0x1a05110846c0d028,0x808b80681444b70,0xb8356c05010100a8,0xf01174b8b5068149,0x8041681458040e0b,0x41a05148100a120b,0x97416052e9710cb4,0x691948040903c0a,0x2022d004120b870,0xd0101038b306a,0xc80a22022c404120,0xba813e0501010380,0xf02ac02417068155,0xe120b83404125728,0xa0202070401a02,0x86154170691804ad]))
|6=>(OfNat.ofNat (packedNat [0xb9341a750116868,0xd010482ec802808,0x384e268340a220bb,0x1c1a0501004e2460,0x10485e2006814041,0x26301458120bb141,0xa020905d880d61a6,0xc241707814f8120b,0x8348c023a2fc1a05,0x1201038326100824,0x1706808084947034,0xa29022101e05010,0x109a7d012a824170,0x68780404460c80a0,0x260b001a02022217,0xe050105cfcbe0781,0x536120b81404120b,0xaf40a120b9b9780d]))
|7=>(OfNat.ofNat (packedNat [0x687936040b81424,0x1769ad01a052b808,0x80d02930c87a0d1,0x180a02490c80a7c0,0x91701a023a049a45,0x2010482e7f218142,0x4173d0348c0222a5,0x984020905d780d68,0x80824170681404d0,0x3d00824174d1c81e,0x120b980be0d3133c,0x2417068140417670,0x34c4120bb3404120,0xb974000547808081,0xc6614804120bb301,0xa05010041a070101,0x9a05012e8d2cb2b,0x32804040b81404c9]))
|8=>(OfNat.ofNat (packedNat [0x10482e7206b740a,0x20905c1a0511144,0x2ebc6e0340a120ba,0x981a0526048b8b40,0x6b6c0a0202048340,0x5010102e4d069980,0x4040905c1a050105,0xcbabc0698844da09,0x5c0a020905db232,0x280824d80681444,0x4c42034c4d70b974,0x1e750280808cc078,0x140404168340a020,0x8c80a7c020481a0,0x511084ce4302808b,0xa5c068482e106b01,0x404120bb541a0509,0x5da856650082e5d]))
|9=>(OfNat.ofNat (packedNat [0x4481404120b971b8,0xd0280808120681c,0x4120b895c20d730,0x824170681424175,0x3394ac05010482e7,0x20d01404045505c1,0xa05020482e100680,0x8241772125c60d02,0x8082417068148002,0x7105dc20d0280824,0x17168340a4c02049,0xc046028082417068,0x14444c010101a050,0x10102488068788c0,0x2092b81ac3010482,0xe25190340a120bae,0x5980d0289024170d,0x3780a020905c5a05]))
|10=>(OfNat.ofNat (packedNat [0x28482ef4798340a,0x202049e44602808,0x2417788c81a05010,0x84241a0681536120,0xb835de05010482e0,0xd4080824172e0348,0xc0501011ca0d3e80,0x824170681404120b,0xbb81a05010119217,0x768340a020905c5a,0xd02808081c06814,0x4120bbb01a05010,0x10384e0681404eb0,0x905c0a020905dd4e,0x9068142417740340,0xa22260101a050132,0x4241706814f8120b,0x9701a0501049ce5c]))
|11=>(OfNat.ofNat (packedNat [0x7d1588c020905dbe,0xd0293004127c834,0xc446010482e05010,0x482e69433781a1e0,0x10482e2d19014441,0x20b8340a2c0905cd,0x60f0280824172f83,0x40af801048b80d02,0x9300404710680a02,0xb9750c0d3101424,0x17370c81a0501011,0x7e0d0280808f70b8,0x348c020905dec0d5,0x90082417798c80a0,0x20905cdc0d02848a,0x217530340a022e97,0x10c0d3a878045a0b,0x835ea05010482e0d]))
|12=>(OfNat.ofNat (packedNat [0x905cf43206a3404,0x120bc08640501048,0x2e0d0280a0217728,0x340a02800482e0d0,0x280824177f834241,0x72e180be0d0f30c0,0x4120b8340a020905,0xc200d028482ef441,0x340a0202049a00d,0x13f824170e0340a,0x4c7e8482e3202808,0x24ba600340a4c093,0x894a320681404043,0x48340a027b85d7ef,0xc1901404120b8343,0xc05010111c0d0286,0x8120b835f60501,0x482ee1028082417]))
|13=>(OfNat.ofNat (packedNat [0x834146405010482e,0xd02808241762834,0xa020b9a5961a190,0x1404040938434050,0x10482e0d02808081,0x7348340a020905e0,0x8dc0280824176f83,0x480020905c3a0d02,0x8082417348c81a02,0x905dac1a1901404,0x1281834ea023a048,0x2e0d230080874090,0x340a4c648482e1a0,0x2bf404120b8680a0,0x25505c1a050905c2,0xe10681404122e03,0x43c020939c2e0501,0x482edf44034c405]))
|14=>(OfNat.ofNat (packedNat [0x1681444120baf05a,0xd02888241706814,0x30120b834c446010,0x48b80d0280a1c172,0xe8340a020205cdc0,0xd028082417868140,0x4120ba18e40d2300,0xa18120b834c44626,0x482e0d038082417,0x2f8340a120ba0928,0xd028082417370c8,0x1a1e02808080d858,0x1404120b8340b0a0,0x10482e0d02808241,0x7848681a05014202,0xe1a0280825070b8c,0x80a02092e94c0209,0x5c000d23008242f]))
|15=>(OfNat.ofNat (packedNat [0x1012060d2301424,0x17220b5980501048,0x2e0d3a8140412570,0x34c40526048b80d0,0xf11804120b8340a0,0x2091fd7c32028082,0x4df2e0348c023a04,0x81a05010482e7221,0x81404040905c1a05,0x10482ea02b07804,0x120b9c81a0501010,0x3886068142417532,0xd01a050905d4a6e0,0x681624020905e220,0x5260082417880340,0xa020905c5a0d0288,0x80817068780a027b,0x85c1a05010482f0f]))
|16=>(OfNat.ofNat (packedNat [0x2b32804120b8c81b,0x17010482efc06814,0x98120b8340acf010,0x482e0d0288a2c120,0xb81404040905ca60,0xd3100a28120b8340,0xa020204a2a0d0280,0x8241766c141a0501,0x102e0d029002417,0x5a0688c05013c02e,0xd02930041268414,0x1a05010482e05010,0x482e252683404fe0,0x905cba0d23008241,0x7390340a028a0482,0xe0d230082417500c,0x81a0501049460d02,0x93024a5898681a05]))
|17=>(OfNat.ofNat (packedNat [0x20709a0d2300825,0x200b81404120bb7c,0x9a0d0f008241724b,0x301a050147c2e0d0,0x280824178f014041,0x24e05dbe0d650140,0x4040b8b41a050905,0xd080d02888251d4a,0x680a020905ce40d,0x280824178e46c1a,0x5010482e0d02808,0x24178d0c80a7c090,0x5c1a05010482f192,0x181404120b870646,0x2010482e48068149,0x804092d01a050132,0x42e5d0d03404128c,0x2381a1e010102e25]))
|18=>(OfNat.ofNat (packedNat [0xb8c80a0202049be,0xd3135c241770814,0x4120bb7c04120b9,0x709025068482e1c3,0x17c1a62260482e4,0x8028e804040905c6,0x40d02808247f0280,0x824173fa181a0511,0x8c817190140412,0xbc91980d0280824,0x1706808241730124,0x1a1e010482f23068,0x1499220905c1a050,0x104a421706988c20,0x40905c1a040905cc,0x5f2181498120b95,0x864020905d100d02,0x8082e5d348340a02]))
|19=>(OfNat.ofNat (packedNat [0x104a5417069180a,0x2093c02e0d02888,0x4120bca41a05110,0x824175d0340a026,0x48482e2d02808241,0x76f8c81a05010102,0x4e10681404120b83,0x40a02020482e2506,0x81444020905d7c0d,0x2bf404120bb301a,0x501010381a19014,0x412948340a02090,0x5e500d0280a4e120,0xb8343c05930482e0,0xd6501404172e8340,0x4120b9c5400d0280,0x8241792b300a0209,0x5c9a1a0681404c1]))
|20=>(OfNat.ofNat (packedNat [0xb8340a4c010482e,0x250681498020905d,0x7e0d028082417370,0x348c020905c4a0d0,0x288804120b99c1a6,0x2029302417069180,0xa020905cbecc0d03,0x40a020905c1a0501,0x482e69190140412,0xbb7c1a460280824,0x176f8340a0202048,0x2ea0069880a4c010,0x482e0d0280824170,0xe0941a027f0482e0,0xd0f1180a020905c1,0xa620f01404120b83,0x4c446010482e0d02,0x80824178c3941a05]))
|21=>(OfNat.ofNat (packedNat [0x2181404120b8343c,0x20905c4a0d23014,0x4120b920340d02c,0xac04120b8340a020,0x905cba25190340a2,0x2010482e0d028080,0x8360905e0a0d0280,0x82417068780a0209,0x5ce40d0280a2812,0xb83564460280824,0x17068788c020905c,0x1a05010482e720d0,0x340a020905cfeb50,0x681444020905c1a0,0x5010482ea0068780,0xa020205df80d0280,0x82417168340a2209,0x5cac0d028880412]))
|22=>(OfNat.ofNat (packedNat [0x280808120b8c81a,0x50104a3e1716834,0x8c05010482e0d028,0x8804120b8941a052,0x60482ef406988c21,0x20b83424173017c1,0xa051100824177203,0x40ad7010482ecc06,0x81404120b8c81a05,0x10482e88069180a,0x20905d2c1a06814,0x4120baf81a05010,0x482e710681404610,0x20482e0d028086c1,0x20bb301a05010102,0x41706b280a020905,0xc1a0526008241791,0x8340a02020482e71]))
|23=>(OfNat.ofNat (packedNat [0x681404,0x120b8340a0230848,0x2e0d0280824176f8,0x343c05010482e0d0,0x280824178e8340a0,0x20905c1a05010482,0xe250681404040905,0xc1a4602808241706,0x9880a020905c5a0d]))
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>(OfNat.ofNat (packedNat [0x12300f300c3,0x93006300330003]))
|3,0=>(OfNat.ofNat (packedNat [0x111410d410941054,0x10140fd40f940f54,0xf140ed40e940e54,0xe140dd40d940d54,0xd140cd40c940c54,0xc140bd40b940b54,0xb140ad40a940a54,0xa1409d409940954,0x91408d408940854,0x81407d407940754,0x71406d406940654,0x61405d405940554,0x51404d404940454,0x41403d403940354,0x31402d402940254,0x21401d401940154]))
|3,1=>(OfNat.ofNat (packedNat [0x1454,0x141413d413941354,0x131412d412941254,0x121411d411941154]))
|4,0=>(OfNat.ofNat (packedNat [0x284527f527a52755,0x270526b526652615,0x25c52575252524d5,0x2485243523e52395,0x234522f522a52255,0x220521b521652115,0x20c5207520251fd5,0x1f851f351ee51e95,0x1e451df51da51d55,0x1d051cb51c651c15,0x1bc51b751b251ad5,0x1a851a3519e51995,0x194518f518a51855,0x180517b517651715,0x16c51675162515d5,0x1585153514e51495]))
|4,1=>(OfNat.ofNat (packedNat [0x3c453bf53ba53b55,0x3b053ab53a653a15,0x39c53975392538d5,0x3885383537e53795,0x374536f536a53655,0x360535b535653515,0x34c53475342533d5,0x3385333532e53295,0x324531f531a53155,0x310530b530653015,0x2fc52f752f252ed5,0x2e852e352de52d95,0x2d452cf52ca52c55,0x2c052bb52b652b15,0x2ac52a752a2529d5,0x2985293528e52895]))
|4,2=>(OfNat.ofNat (packedNat [0x4415,0x43c54375432542d5,0x4285423541e54195,0x414540f540a54055,0x40053fb53f653f15,0x3ec53e753e253dd5,0x3d853d353ce53c95]))
|5,0=>(OfNat.ofNat (packedNat [0x5bd65b765b165ab6,0x5a5659f659965936,0x58d65876581657b6,0x575656f656965636,0x55d65576551654c5,0x5466540653a65346,0x52e65286522651c6,0x5175512550c65066,0x50064fa64f464ee6,0x4e864e264dc64d66,0x4d064ca64c464be6,0x4b864b264ac64a66,0x4a0649a6494648e6,0x4886482647c64766,0x470646a6464645e6,0x4586452644c64466]))
|5,1=>(OfNat.ofNat (packedNat [0x7396733672d67276,0x721671b6715670f6,0x709670546ff66f96,0x6f366ed66e766e16,0x6db66d566cf66c96,0x6c366bd66b766b16,0x6ab66a5669f669a5,0x695568f668966836,0x67d66776671666b6,0x665665f665966536,0x64d66476641663b6,0x635662f662966236,0x61d66176611660b6,0x60565ff65f965f36,0x5ed65e765e165db6,0x5d565cf65c965c36]))
|5,2=>(OfNat.ofNat (packedNat [0x8b568af68aa58a46,0x89e68986892688c6,0x8866880687b58756,0x86f68696863685d6,0x8576851684b68456,0x83f68396833682d6,0x8276821681b68156,0x80f6809680367fd6,0x7f767f167eb67e56,0x7df67d967d367ce5,0x7c867c267bc67b66,0x7b067aa67a4679e6,0x7986792678c67866,0x780677a6774676f5,0x7696763675d67576,0x751674b6745673f6]))
|5,3=>(OfNat.ofNat (packedNat [0x9b569af69a96,0x9a3699d699769916,0x98b6985697f69796,0x974596e696869626,0x95c69566950694a6,0x944693e693869326,0x92c69266920691a6,0x914690f590969036,0x8fd68f768f168eb6,0x8e568df68d968d36,0x8cd68c768c168bb6]))
|6,0=>(OfNat.ofNat (packedNat [0xb565b4f7b496b436,0xb3c7b357b2e7b286,0xb217b1b6b147b0e6,0xb077b007afb5af56,0xaee7ae77ae07ad97,0xad27acc6ac57abf6,0xab87ab26aac6aa57,0xa9e7a986a926a8c6,0xa866a7f7a787a717,0xa6b6a656a5e7a586,0xa517a4a7a446a3e6,0xa377a307a297a227,0xa1d5a167a0f7a096,0xa0279fc69f579ee7,0x9e779e169db69d56,0x9cf69c879c179bb6]))
|6,1=>(OfNat.ofNat (packedNat [0xb7b7b747,0xb6d7b667b606b5b5]))
|7,0=>(OfNat.ofNat (packedNat [0xbb16,0xbab6ba56b9f6b9a5,0xb946b8e6b886b826]))
|8,0=>0xbb75
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 300 then fld (dictB (i / 512) (i / 32 % 16)) 32 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 16 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x28100687b0105d0,0x905d0691b0285d01,0x490905d0687a010,0x490f05d0137d0905,0xd02848068793085d,0x28080905d028120,0x905d0685d0f05f01,0x49190880105d010,0x490905d0905d2604,0x9010490905d01049,0x2810010490905d0,0x10130905d0280a02,0x8090280a0905c028,0x9230480905d0281,0x2010130280a0685c,0x105d0905d0685e0,0x105d028090905d02,0x85e0285c0f05e010,0x5d0101102a390285,0xe01049010130905d]))
|1=>(OfNat.ofNat (packedNat [0x2bc1068480105d0,0x105e0280a0905d0f,0x5e010490105d010,0x110905c0687b0104,0x9230480f05f01049,0x280a069890285e0,0x10490905d0905d0f,0x9010490105d068,0x170104902b7d0285,0xf0280a0105d0685e,0x280a02bc3068480,0x688a0f0090f05d01,0x490bb7d0105d010,0x5d01049233c10684,0x80105d0905f0105e,0xf05d0280a028090,0x105d0105d1901602,0x85d010490905d090,0x5e0905e068790905,0xc01049068150105d]))
|2=>(OfNat.ofNat (packedNat [0x68480f05f0285d0,0x10490285d0101201,0x5d0280a0f05c260,0x490d05d0f05f0681,0x5010490285f01049,0x684a010490285f0,0x1049010100905d09,0x5d0105d0280a068,0x170687b010490905,0xd0687b010490905c,0x280a010490280b0,0x10490905d0104902,0x8090bb7d01049010,0x49028090280a1908,0x80105d010490285e,0x10490285f010490,0x6848010490285d01,0x4906879010110f0,0x5d010100137d0285,0xf028100104906848]))
|3=>(OfNat.ofNat (packedNat [0x68480105d0685f0,0x10490685c0104902,0x80a068090284b090,0x5d01049068790104,0x90280a0905d0105e,0x10490137d0284b0,0x10490f05d0101209,0x5d0285f01049090,0x5c02809010490905,0xd0f05d0104901049,0xbb7d06817068160,0x2809028080905d01,0x490f05f01012010,0x490285f010120105,0xd0285f0104930849,0x28080905d0905d0,0x10490f0090687901,0x490905c0105d010,0x490905d0284b0280,0xa010490f05d06849]))
|4=>(OfNat.ofNat (packedNat [0x104906817010490,0x6878010490905e02,0x80a0104901010090,0x5d010490f00b0104,0x90bb7d0284b23009,0x285d010490691a0,0x105d0f05f0104901,0x49010120905d010,0x490905d069890280,0x9068150104901049,0x105d0105d0f00b0,0x104906816010490f,0x5c0104901049028,0x906817010490f05,0xf010490285f01049,0x684b0105d010120,0x905d068150105d09,0x5c0280a0280a028,0x5d01049068150280,0x9010490105e0280a]))
|5=>(OfNat.ofNat (packedNat [0x28,0x80284b010490105,0xf0280a0105d02809,0x28090905d230480,0x105d068090104901,0x490105f02809028,0x8068170687b0104,0x93085d028080f05d,0x2300b0f05e0285e0,0x10490905d0280809,0x5d010100905d090,0x5d30849028080691,0xb0105d0905d0280b]))
|_=>0
def opOffB:Nat → Nat → Nat
|4,0=>(OfNat.ofNat (packedNat [0x5440000000a0,0x84c4242000000000,0x111079000000,0x38400000,0x68830416200005,0x800000000000000,0x9100000000,0x3900000000,0x6100001440000000,0x460000000,0x0,0x44000,0x4000000]))
|4,1=>(OfNat.ofNat (packedNat [0x120,0x8000000000000088,0x8000000000084400,0x100800000000,0x0,0x3a600000000,0x38200000000000,0x0,0x1b10,0xd080003220000000,0x0,0x3021710000584000,0x0]))
|4,2=>(OfNat.ofNat (packedNat [0xa4c0000000,0x0,0x0,0x2630000000000,0x2510000000000000]))
|5,0=>(OfNat.ofNat (packedNat [0xc025f12e9,0x16c8000000000168,0x4b220002c095c4ac,0x25512919444a024f,0x100013840004d126,0x80009624a100011,0xcc00046100011448,0x8243121080008043,0xf10000f840003d10,0xf047623831b88,0xd840000001a88d04,0x3311908c44000,0x2e31688b04000000]))
|5,1=>(OfNat.ofNat (packedNat [0x489,0x80011e48d2000000,0x1164000000000112,0x4881438800000086,0x1000000000000042,0x8800106482100000,0x408a004f,0xa67b23d080000007,0x820001dc4ec27513,0x990000e427023789,0xb84d666a10001a08,0xce26520000000c64,0x1884000611]))
|5,2=>(OfNat.ofNat (packedNat [0x6508001922000640,0x8000000000638800,0x630b14400,0x620b0c4000c2,0x1608afc978600000,0x5d12e,0x8000b710002d856,0x84b225812b89584a,0xa20002a44000a815,0x38a9840000005210,0x1462a124f92785,0x3849b14c926052e2,0x12a4941]))
|5,3=>(OfNat.ofNat (packedNat [0x1d8200000,0x3ac40000000003a,0x85d22e7200000000,0xe6172138c5c240,0x7008001be2de10,0x3744000da30003,0x644000d816b8b585,0xa84d310000001a24,0xce3668b305962000]))
|6,0=>(OfNat.ofNat (packedNat [0xaa8d4caa25501a78,0xd3869854b1a4951c,0xa8c3442a11504400,0x13f29e94eca72538,0x19b14d4666531298,0xcb8a5852a2948c9,0xca4a523290948063,0xe31e18e1468a3051,0x628a8c5062451028,0x71430a145082838c,0x14a083022808c005,0xfc4fc27d13e45ee4,0xf527993c49de4ed2]))
|6,1=>(OfNat.ofNat (packedNat [0x2bc5,0x5c2ad8d686b05562]))
|7,0=>(OfNat.ofNat (packedNat [0x1661b28d906c62,0xb108002c23601]))
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 13 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x302f2c2a29262524,0x2321201c19181614,0x131211100d0c0b09,0x806050403020100]))
|1=>(OfNat.ofNat (packedNat [0xa6a28c8b8a878685,0x8381807d746b5957,0x51504e4948454341,0x403d3c3938363432]))
|2=>(OfNat.ofNat (packedNat [0xfffbf3efec,0xdfc6bfbeafadaba9]))
|_=>0
def pmB:Nat → Nat → Nat
|4,0=>(OfNat.ofNat (packedNat [0xc0000000,0x1800000080000400,0x50,0x8000000000,0x604020,0x80000000000000,0x8600040000000000,0x1c000080408000,0x11a000000010,0x208080180000,0x100000000,0x2000010004000000,0x400000000000000,0x42000010000]))
|4,1=>(OfNat.ofNat (packedNat [0x20000000,0xc000000000000,0x800000040000000]))
|5,0=>(OfNat.ofNat (packedNat [0x100040318,0x1838000004010200,0x400006000e0008,0x100000006a7c4816,0xa0000800040b9580,0x908028458c2a0d3,0x8708000800004001,0x100870e1400c00,0x5380020978e5654,0x84001c001060008,0xc002c00200d40820,0x4014810010001003,0xc0b021c00c0804a,0x9518340370208000]))
|5,1=>(OfNat.ofNat (packedNat [0x100001000,0x460834000396,0x6304000e00095085,0x4019008020102280,0x8100001bb201c080,0x200300421000004,0x1c800cf8a802a04,0x7201c400000000,0x106c00100600871,0x1c40a0054027027,0xc6000c006282c081,0x8c0e043800000501]))
|6,0=>(OfNat.ofNat (packedNat [0x9934a6931e,0x7e46098280442180,0x98643221113a5a3d,0xb2336715493a2d93,0x15c905cc6088d016,0x9204443a49a09562,0xdeba8c2cca571056,0x31110a5132ef044b]))
|7,0=>0x418e9934c8621345
|8,0=>8
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 7 (j % 128);fld (pmPalB (k / 32)) 8 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_29,6,runOps true dom_29 (0,roots_29) ops)] else [])++(if pm.testBit 1 then [(dom_7,4,runOps true dom_7 (0,roots_7) ops)] else [])++(if pm.testBit 2 then [(dom_19,4,runOps true dom_19 (0,roots_19) ops)] else [])++(if pm.testBit 3 then [(dom_30,6,runOps true dom_30 (0,roots_30) ops)] else [])++(if pm.testBit 4 then [(dom_11,4,runOps true dom_11 (0,roots_11) ops)] else [])++(if pm.testBit 5 then [(dom_27,5,runOps true dom_27 (0,roots_27) ops)] else [])++(if pm.testBit 6 then [(dom_15,5,runOps true dom_15 (0,roots_15) ops)] else [])++(if pm.testBit 7 then [(dom_23,5,runOps true dom_23 (0,roots_23) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_31 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_29_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_7_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_19_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_30_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_11_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_27_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_15_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_23_32 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_29 6 s (0,roots_29) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_31 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_29_32 h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8)],[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)],[((OfNat.ofNat (packedNat [0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0])),12)],[((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)],[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0,0xf0f00000f0f0])),12)],[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4)],[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_31==dom_31) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_31 goalM v ys):RunD true dom_31 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 7 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 7 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 77 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 77 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_0:∀ i,0 ≤ i → i < 128 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 128 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4_128:∀ i,128 ≤ i → i < 153 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 25 128=true)
private theorem z4:∀ i,0 ≤ i → i < 153 → Z 4 i=true:=(range_split z4_0 z4_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 128 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 235 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 107 128=true)
private theorem z5:∀ i,0 ≤ i → i < 235 → Z 5 i=true:=(range_split z5_0 z5_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 70 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 70 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 9 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 9 0=true)
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
end S_31_32
theorem lowS_31_32:Lower true dom_31 roots_31 goal_31_32 9:=S_31_32.noCircuit
end Case0
namespace Case1
open Search PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def dom_7:=0xff
def roots_7:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0]
def dom_14:=0x5555
def roots_14:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_15:=0xffff
def roots_15:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0]
def dom_22:=0x550055
def roots_22:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_23:=0xff00ff
def roots_23:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 4 0]
def dom_27:=0xf0f0f0f
def roots_27:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_29:=0x33333333
def roots_29:List Nat:=[xs256.getD 0 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_30:=0x55555555
def roots_30:List Nat:=[xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_31:=0xffffffff
def roots_31:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0]
def dom_63:=0xffffffffffffffff
def roots_63:List Nat:=[xs256.getD 0 0,xs256.getD 1 0,xs256.getD 2 0,xs256.getD 3 0,xs256.getD 4 0,xs256.getD 5 0]
def goal_7_0:=0xe8
def goal_7_16:=0xe8
def goal_7_32:=0xe8
def goal_14_48:=0x5440
def goal_15_16:=0xece8
def goal_15_32:=0xeae8
def goal_15_48:=0xfeea
def goal_22_40:=0x540040
def goal_23_32:=0xea00e8
def goal_23_40:=0xfe00ea
def goal_27_32:=0xe0a0a08
def goal_29_32:=0x32222220
def goal_30_32:=0x54404040
def goal_31_32:=0xfeeaeae8
def goal_63_0:=0xfeeaeae8ece8e8e8
namespace S_27_32
def pairsG:List (Nat × Nat):=[(1,3),(1,9),(1,17),(2,3),(8,9),(10,11),(10,26),(16,17),(18,19),(18,26),(24,25),(24,26)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_27.map (· &&& dom_27)
def goalM:Nat:=goal_27_32 &&& dom_27
def NN:Nat → Nat
|2=>2
|3=>11
|4=>8
|5=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0x8e339dbc21bad7fd
|3,0=>(OfNat.ofNat (packedNat [0x9d277db1,0x92b669203734731c,0x262c6e4921b3afde,0x205d852e1c416772,0x16a5493a1288e76e,0x19df92000be1cca]))
|4,0=>(OfNat.ofNat (packedNat [0x9d277db1629e221b,0x4dec4760464d889c,0x3ba977c9256ff944,0x1a9db4f605d02eb9]))
|5,0=>0x9d277db1
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat (packedNat [0xc,0xc0000a000a808,0x808f080f08f0a0f,0xaa000a004040404,0x2020202f0f0f00f0,0xf0a00003030,0x202f000f0c707000,0xf000300f0f00003,0x30000c000ca0a,0xa0a00f0f00f000f,0xc0c0c0c5050a0a]))
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x7104,0x8710487104863883,0x621c41254e209207,0x9082471c4121c412,0x50e2090f3090f20c,0x4e283dcd09182090,0xe222cea09041224e,0x8090e43142418820]))
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>0x19803
|3,0=>(OfNat.ofNat (packedNat [0xb9152264448790,0xd216424839052064]))
|4,0=>(OfNat.ofNat (packedNat [0xaa9416,0x5ac6582af15bab25]))
|5,0=>0x594
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 23 then fld (dictB (i / 512) (i / 32 % 16)) 28 (i % 32) else 0
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
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 12 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 31),wireSAt ((code >>> 7) &&& 31))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_27 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_27 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8)],[((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6)],[((OfNat.ofNat (packedNat [0xcccc0000cccc,0xcccc0000cccc,0xcccc0000cccc,0xcccc0000cccc])),14)],[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xcccc0000cccc,0xcccc0000cccc,0xcccc0000cccc,0xcccc0000cccc])),14)],[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_27==dom_27) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_27 goalM v ys):RunD true dom_27 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 2 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 2 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 11 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 11 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 8 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 8 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5:∀ i,0 ≤ i → i < 1 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 5):∀ i < NN s,bar true dom_27 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
  · exact z5 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_27 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 3 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 5) (h:RunD true dom_27 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_27 roots_27 goal_27_32 6:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_27_32
theorem lowS_27_32:Lower true dom_27 roots_27 goal_27_32 6:=S_27_32.noCircuit
namespace S_7_0
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(2,3),(2,6),(4,5),(4,6)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x3f
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_7.map (· &&& dom_7)
def goalM:Nat:=goal_7_0 &&& dom_7
def NN:Nat → Nat
|2=>1
|3=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>0xd4bda944
|3,0=>0xd4bda944
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>0xf0ccaa
|_,_=>0
def stPool:Nat → Nat
|0=>0x924
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>3
|3,0=>0x33
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 3 then fld (dictB (i / 512) (i / 32 % 16)) 8 (i % 32) else 0
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
def opOffB:Nat → Nat → Nat
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 6 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 3),wireSAt ((code >>> 4) &&& 3))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 5 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>0
|_=>0
def pmB:Nat → Nat → Nat
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 1 (j % 128);fld (pmPalB (k / 32)) 1 (k % 32)
def mkPools (_ _:Nat):List (Nat × Nat × (Nat × List Nat)):=[]
def mkCut (_ _:Nat) (_:Nat × Nat × Nat) (_:List Nat):Bool:=false
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_7 goalM s ys:=by simp [mkCut] at h
def cutRoot (_:Nat) (_:List Nat):Bool:=false
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_7 goalM v ys:=by simp [cutRoot] at h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2)],[((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)],[((OfNat.ofNat (packedNat [0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a])),3)],[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2),((OfNat.ofNat (packedNat [0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0a])),3)],[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2),((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_7==dom_7) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_7 goalM v ys):RunD true dom_7 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_7 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 1 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 1 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 1 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 1 0=true)
theorem checked (s:Nat) (hs:s ≤ 3):∀ i < NN s,bar true dom_7 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_7 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 2=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 3) (h:RunD true dom_7 goalM s xsM):False:=by
  have hmin:2 ≤ s:=by have hl:=run_len h;change 3 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_7 roots_7 goal_7_0 4:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_7_0
theorem lowS_7_0:Lower true dom_7 roots_7 goal_7_0 4:=S_7_0.noCircuit
def isoMv_22_40:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4),((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6),((OfNat.ofNat (packedNat [0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa])),7)]
theorem lowS_22_40:Lower true dom_22 roots_22 goal_22_40 4:=lower_iso isoMv_22_40 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_0
def isoMv_14_48:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0,0xf000f000f000f0])),4),((OfNat.ofNat (packedNat [0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc,0xcc00cc00cc00cc])),6),((OfNat.ofNat (packedNat [0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa,0xaa00aa00aa00aa])),7)]
theorem lowS_14_48:Lower true dom_14 roots_14 goal_14_48 4:=lower_iso isoMv_14_48 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_0
def isoMv_7_32:List (Nat × Nat):=[]
theorem lowS_7_32:Lower true dom_7 roots_7 goal_7_32 4:=lower_iso isoMv_7_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_0
theorem lowS_15_48:Lower true dom_15 roots_15 goal_15_48 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xaaaa,0,1)] (by decide +kernel) (by decide +kernel) lowS_14_48
def isoMv_23_40:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8)]
theorem lowS_23_40:Lower true dom_23 roots_23 goal_23_40 5:=lower_iso isoMv_23_40 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_48
def isoMv_29_32:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2)]
theorem lowS_29_32:Lower true dom_29 roots_29 goal_29_32 6:=lower_iso isoMv_29_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_27_32
def isoMv_7_16:List (Nat × Nat):=[]
theorem lowS_7_16:Lower true dom_7 roots_7 goal_7_16 4:=lower_iso isoMv_7_16 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_7_0
theorem lowS_15_16:Lower true dom_15 roots_15 goal_15_16 5:=lower_slice (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) [(0xff00,2,10)] (by decide +kernel) (by decide +kernel) lowS_7_16
def isoMv_23_32:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)]
theorem lowS_23_32:Lower true dom_23 roots_23 goal_23_32 5:=lower_iso isoMv_23_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def dzo_22_8:=0x55005500
def gzo_22_40_8:=0x54004000
theorem lowSh_22_40_8:Lower true dzo_22_8 roots_22 gzo_22_40_8 4:=lower_iso (d1:=dom_22) (roots1:=roots_22) (T1:=goal_22_40) [(dom_22,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_22_40
namespace S_30_32
def pairsG:List (Nat × Nat):=[(2,6),(4,6),(10,14),(10,26),(12,14),(12,28),(18,22),(18,26),(20,22),(20,28),(24,26),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0xfff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_30.map (· &&& dom_30)
def goalM:Nat:=goal_30_32 &&& dom_30
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
    (if pm.testBit 0 then [(dzo_22_8,4,runOps true dzo_22_8 (0,roots_22) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_30 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    obtain ⟨_,rfl⟩:=he;exact cpcs (by decide +kernel) lowSh_22_40_8 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dzo_22_8 4 s (0,roots_22) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_30 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowSh_22_40_8 h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8)],[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2)],[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_30==dom_30) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_30 goalM v ys):RunD true dom_30 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_30 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
private theorem z2:∀ i,0 ≤ i → i < 0 → Z 2 i=true:=by omega
private theorem z3:∀ i,0 ≤ i → i < 0 → Z 3 i=true:=by omega
private theorem z4:∀ i,0 ≤ i → i < 0 → Z 4 i=true:=by omega
theorem checked (s:Nat) (hs:s ≤ 4):∀ i < NN s,bar true dom_30 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i=true:=by
  intro i hi;change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool true e.1 e.2.1 (s'-1) (stepOp true e.1 e.2.2 g) zs) s i=true;rw [← barP_eq];interval_cases s
  · exact z0 i (Nat.zero_le i) hi
  · exact z1 i (Nat.zero_le i) hi
  · exact z2 i (Nat.zero_le i) hi
  · exact z3 i (Nat.zero_le i) hi
  · exact z4 i (Nat.zero_le i) hi
def RootG (s:Nat):Bool:=scr true dom_30 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in theorem rootChecked:span RootG 2 3=true:=by decide +kernel
theorem proper_failG:∀ zs ∈ xsM.sublists,zs ≠ xsM → unorientedCov pairsG zs=false:=by decide +kernel
theorem noRunFull (s:Nat) (hs:s ≤ 4) (h:RunD true dom_30 goalM s xsM):False:=by
  have hmin:3 ≤ s:=by have hl:=run_len h;change 4 ≤ s+1 at hl;omega
  have hr:=span_ok rootChecked s hmin (by omega)
  unfold RootG at hr;rw [scr_no pool6G h,Bool.false_or,Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found,Bool.and_eq_true,decide_eq_true_eq,List.isPerm_iff] at hf
    exact bar_all (pairs:=pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _=>rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit:Lower true dom_30 roots_30 goal_30_32 5:=lower_of_search (pairs:=pairsG) (by decide +kernel) proper_failG noRunFull
end S_30_32
theorem lowS_30_32:Lower true dom_30 roots_30 goal_30_32 5:=S_30_32.noCircuit
def isoMv_15_32:List (Nat × Nat):=[((OfNat.ofNat (packedNat [0x2222222222222222,0x2222222222222222,0x2222222222222222,0x2222222222222222])),1)]
theorem lowS_15_32:Lower true dom_15 roots_15 goal_15_32 5:=lower_iso isoMv_15_32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_16
def dzo_14_16:=0x55550000
def gzo_14_48_16:=0x54400000
theorem lowSh_14_48_16:Lower true dzo_14_16 roots_14 gzo_14_48_16 4:=lower_iso (d1:=dom_14) (roots1:=roots_14) (T1:=goal_14_48) [(dom_14,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_14_48
def dzo_23_8:=0xff00ff00
def gzo_23_40_8:=0xfe00ea00
theorem lowSh_23_40_8:Lower true dzo_23_8 roots_23 gzo_23_40_8 5:=lower_iso (d1:=dom_23) (roots1:=roots_23) (T1:=goal_23_40) [(dom_23,8)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_23_40
def dzo_15_16:=0xffff0000
def gzo_15_48_16:=0xfeea0000
theorem lowSh_15_48_16:Lower true dzo_15_16 roots_15 gzo_15_48_16 5:=lower_iso (d1:=dom_15) (roots1:=roots_15) (T1:=goal_15_48) [(dom_15,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) lowS_15_48
namespace S_31_32
def pairsG:List (Nat × Nat):=[(1,3),(1,5),(1,9),(1,17),(2,3),(2,6),(4,5),(4,6),(8,9),(10,11),(10,14),(10,26),(12,13),(12,14),(12,28),(16,17),(18,19),(18,22),(18,26),(20,21),(20,22),(20,28),(24,25),(24,26),(24,28)]
def r1sG:List Nat:=pairsG.map Prod.fst
def r2sG:List Nat:=pairsG.map Prod.snd
def mpG:Nat:=0x1ffffff
def pool6G:List Nat:=[]
def xsM:List Nat:=roots_31.map (· &&& dom_31)
def goalM:Nat:=goal_31_32 &&& dom_31
def NN:Nat → Nat
|2=>6
|3=>62
|4=>115
|5=>222
|6=>75
|7=>13
|8=>1
|_=>0
def HT:Nat → Nat → Nat
|2,0=>(OfNat.ofNat (packedNat [0xe77c113d96e715fd,0x84cb36aa663b4323,0x34479cc605723852]))
|3,0=>(OfNat.ofNat (packedNat [0xe32cdce9e0cd7b16,0xd171fbe8b2e2f8c8,0xb0c90f16a2441b20,0xa19e3d119d52e25d,0x9638e8f58f0bf331,0x8a2547fd885e2149,0x7c9d94346efd2480,0x6bc1fc306a0eddb6,0x69291a4f65209d8c,0x64fcbe5762a447cb,0x6007a545580ade97,0x5624d83454ef1fcd,0x5479c62b504648be,0x502b1f844fa8a7b0,0x4fa21a7a4c20948e,0x459b0020453a62ed,0x43f161e641e660d1,0x3d0885cf3c9e43bf,0x3888b02338699e29,0x37b3523934fa787c,0x2c37be842be1abbd,0x29d51d5827c9cf0c,0x1fe146271b8d6a36,0x162e3dfa1497a16f,0x1404f3c6113ae457,0xfdec44e0c5d915f,0xbcfa8760ae8822e,0xaa47b1c0aa2e4e7,0x9f54dd609aa8c6b,0x96f711c05d9543b,0x5a09c64027fb23f]))
|4,0=>(OfNat.ofNat (packedNat [0xf88b121b,0xdd410db8d1133626,0xcbaf6331c42589c3,0xa802f718a50e0bf3,0xa48506e994aaf750,0x8dcf8e0488b92791,0x8735da29852c4328,0x812ed8c17eb809c7,0x7d3494bd7d0379b2,0x7ca8998d79744425,0x71dee69470e14392,0x70b6af5d6edf4c7f,0x6dccdf3c6836d176,0x680bd06166c71628,0x632c3f6862d35b04,0x5edf5ed35dee6f82,0x5d9be30f5b55ee48,0x5b3d5e5a59d04230,0x596b636c58ab1b42,0x5540f7d4545d46ed,0x520a3541505f26cf,0x4fc7e1b54bb0aa55,0x45f6563a45a1e545,0x453a7c9d452eadf5,0x44cbf1e541eadb97,0x41e662fb4111b6ca,0x407e69993f9b53ee,0x3de68bad3d888e26,0x3d653f3b3a2f451f,0x37d5d05836d7ea17,0x3610e05d349b1be1,0x345eac4a3443d1e4,0x33c16527337d731c,0x3315cc0a31e2e26c,0x3174431d3021862a,0x2dd40b4e2d42133f,0x2c42e0902a085bc3,0x2908c2e8280b5b07,0x2793b32626ce8ca3,0x26baa6e32654e857,0x24b1d5e4216bd392,0x2111e3011f87dcae,0x1f6224961e12d587,0x1de0f1b11ddd9ddd,0x19a473f818eb8021,0x18e1f7071888265b,0x177d0234161207c6,0x150b652514d2b56f,0x1078bbb51001684c,0xf1a9c9d0d09ca81,0xc94a4800a852818,0x88523ac08812045,0x6f32a2006cd007a,0x66dc74906666ee2,0x61ff50f05ac74cf,0x50e3e9c0467e2ff,0x33e8ad102dd8e9a,0x13a84690117afc3]))
|5,0=>(OfNat.ofNat (packedNat [0x4944f59948773af6,0x47ce092a4788f640,0x468606aa439f9758,0x438d030242583418,0x40d49df040b2d5c1,0x40b2036a400caa23,0x3ebdd55e3e0ba5b2,0x3dd1a5683d867f14,0x3d1825783cde142f,0x3bb685e83b7e67fa,0x3acc6e253a6d6f52,0x3a5d899839670347,0x38f920f13814d908,0x36eb5069354cd925,0x353d53f734ff6990,0x342144112fc8dae0,0x2f43fc842d92e009,0x2d57fd142be20dff,0x2b373e1f2b248991,0x2a48467c29b4f935,0x28ae69ed28a153a5,0x274dc3c3254f218d,0x24fe9f8024e35330,0x24c46c4d241dcca4,0x241cb7b22326eae9,0x21d08c112175128f,0x1febdd111fbc8425,0x1fb84f691f55dfec,0x1f4f26e11e489d4d,0x1e0f4f6c1dee9d27,0x1de8f2ad1d3ce97e,0x1cd6d2541c77b5a0,0x1b1d04c31a7f49c8,0x19927a8f198ce1f3,0x192a467a190b5d3b,0x18d1621618c50e08,0x18b5b64f1855f9d3,0x17f89e0017684dce,0x1662ba7b1542f2b8,0x148e088014585197,0x1400b75b13a7d2f7,0x1372f57212ef47ae,0x12e256e812673055,0x11f92a861175bbd5,0x10d02a8710410323,0x103ee1de1026e1e3,0xf3e81490e9b5341,0xd9ce5310cf23483,0xc287cef0bc415b8,0xb0e103c0ad15a45,0xa8ca5f60a5a15d8,0xa4954ce0a09a330,0x9b7f91f09a0ff5b,0x9966c850964c278,0x8aa2e5a086f8f48,0x790264206d064e8,0x68126b9063fd312,0x5a7cb26055aab69,0x53466f8049b9c2d,0x42604df03d50302,0x304148201f1297d,0x1e69cb301d69399,0x145c58201041bab,0xafdc2100a7504a]))
|5,1=>(OfNat.ofNat (packedNat [0xf3646964e99d8a4c,0xe9148542dc924058,0xdc17eff7da867c97,0xd9331fc3d18c4d1f,0xcfe24645c6a4dd9c,0xc4a6440fc427da71,0xc2afcbabc15dd4f2,0xbfe3b222bfd86441,0xbceebcd0b44642d4,0xb437c42faf1e9219,0xac3c1109a951d62c,0xa7ad298ba54be7ee,0xa4ce50bca2643d33,0x9df08a979ce1902a,0x992da287977c37b9,0x94e5febc91d217e6,0x8f8f1b778f21023d,0x8c8113df8c2d4720,0x874309d9867bd426,0x83cea023801484ee,0x7f0f2a6c7ea82caf,0x7e66eb0d7a19de63,0x78786220786518b6,0x78180520751696de,0x749ffdb872885be1,0x712a8d6570e14392,0x70d611ff70bc8ac8,0x6f92c96d6f7717e5,0x6ae466b068548ee6,0x682e065f65fb51eb,0x645efea86414b3a5,0x6364827b63400eac,0x62eca9e46256342b,0x618f5f4a610b5fed,0x5f25078f5d8f4780,0x5cf8c63e5cf6f3ef,0x5c0c808d5b7132d6,0x56b9bb40566ad211,0x5631218c528f7f79,0x51ab89e250c95184,0x4fc7e1b54f098177,0x4e7506584e1d02df,0x4dc7e76c4c919c03,0x4b82a8794b5e1c38,0x4b1446704aebb286,0x4a82231849df6f92,0x49c04ff549a1fa39]))
|6,0=>(OfNat.ofNat (packedNat [0xee573519,0xe7c60b1dce52c4fa,0xc6a4dd9cc41b66cb,0xb58372c9b44642d4,0xaf753242ae051815,0xabea8af4a2ce3168,0x98e3564c989ce8d7,0x93b7475f91863ebb,0x8cc90b2686981ddb,0x7f5bec7e79238a6e,0x77f7b44a75d43412,0x745f33c174064f5d,0x71732e19712a8d65,0x6f92c96d6b1cb35a,0x668a76c9642830f2,0x5dd68d6a5cf6f3ef,0x5cc01e274e0ae47e,0x4c535ece472e25f7,0x466611f241ecc337,0x3f1826db3ed81f4c,0x3ebdd55e3abf1546,0x35cd937131c1c236,0x2f79e7db2f61f1a4,0x2ee8d5252e160c32,0x2d9fc0262ae9b583,0x28ec7d1328c79243,0x28ae69ed289999ce,0x241cb7b222fed1a0,0x22c5a1b520f514d6,0x1fc249c41fa24f53,0x1c25b9451b017318,0x1a79258e17f89e00,0x17f3b30d16032cd5,0xd7a72cd0d59fc0a,0xa8ea06009a0ff5b,0x89d02fa08088c37,0x728aace05f43a9b,0x3d43e99017e3b29]))
|7,0=>(OfNat.ofNat (packedNat [0xd5d7a2ce,0xaacb8ff0974979bd,0x894af9796ec079dc,0x6432baff34b0cb8f,0x2c56ab271f16380d,0x1495c9760d59fc0a,0x9e2bbbd090d6eb4]))
|8,0=>0x1f16380d
|_,_=>0
def dictB:Nat → Nat → Nat
|0,0=>(OfNat.ofNat (packedNat [0x3fc03fcffaaffaa,0xaa00aa00cccccccc,0xaffaaffaaaa0aaa0,0xff00fffcffffaa88,0xffccffccf0f0f0f0,0xeeaaeeaa0000ffaa,0xc3c0c3c000fc00fc,0xffffaaaaeaeac0c0,0xffc3c0c0fcfcfcfc,0xf000f000333c333c,0xc3c33c3caaaaaaaa,0x1616161696969696,0xff00ff00eaeaeaea,0x303fcfc55aa55aa,0x3c3c3c3cffff0000,0x666666660ff00ff0]))
|0,1=>(OfNat.ofNat (packedNat [0x5a5a5a5a44444444,0x222222220f0ff0f0,0xffff00fc5555aaaa,0xcc30cc300f0c0f0c,0xffeac0c0eeeceeec,0xcffccffc0cc00cc0,0xf600f600152a152a,0xfafafafaa0a0a0a0,0xff000300ffffcccc,0xfafaf8f8eeeeaaaa,0xffc0ff303333cccc,0xaaaa33cc33cc,0xff030000c0c0eaea,0x55550000ffff0330,0xdededede48484848,0xcc32cc32c0c0c0c0]))
|0,2=>(OfNat.ofNat (packedNat [0xfefcfefcecececec,0x1212121204040404,0xb700b7001515aaaa,0xc3c2c3c254fc54fc,0x50705070fcfcfffc,0x300030007700770,0xff00000033303330,0xf0f0c0cfcfca8a8,0xffaa0000c0c03030,0x3030c0c3e3c3e3c,0xffffaa0098989898,0xe0e0e0e14143c3c,0xeca0eca0fffffcfc,0xfcfc00003c3c3f3c,0xfefe00001e1e3c3c,0xff00aacccc0000]))
|0,3=>(OfNat.ofNat (packedNat [0xfe00fefff8fff8,0xccccfafa33323232,0x606060630333030,0x33323332fffcfffc,0xff00fff000003030,0xaaaa0000fafaf0f0,0xe0c0e0cffffaaa0,0xffc0ffc00f0a0f0a,0xc8c8c8c833223322,0xff0eff0e0f000f00,0x11114444fffff0f0,0xf0f00000fff0fff0,0xfaaafaaaeeeeeeee,0x888888881e1e1e1e,0xfc00fc003f3c3f3c,0x303030300c0c0c0c]))
|0,4=>(OfNat.ofNat (packedNat [0xfc00fe00cfcfcece,0xfcfcaaaa54545454,0xffff888803020302,0xfafaaaaa55555050,0xc8c8c0c0ffeeffee,0xcc00cc00aa88aa88,0xfe00aa0a0a0a0a,0xfe00ff0000000e0e,0x77777070fefefcfc,0xffffff0000fcfcfc,0xffabff00ff03ff00,0xf8f88888ffaaaaaa,0xfefefefefcfffcfc,0x303000032323232,0xfca8fca833333030,0xfcfc00aa00aa]))
|0,5=>(OfNat.ofNat (packedNat [0xffff0a0a33330000,0xf0f0fafa51505150,0xc0f0c0ccdcd0000,0xfe00fe00c0eac0ea,0xffff0000fffcfc,0x54ff0000f3f0f3f0,0x1030103003033030,0xf6f6f6f6a8a8a8a8,0x56565656ccffcccc,0x55005500ffaaff00,0xaaaaa0a046464646,0x3030c0c015150000,0xaaaa8888ffffc0c0,0xccccffccff0cff0c,0xfefefafaa0a0,0xffff0c0cf0f0fff0]))
|0,6=>(OfNat.ofNat (packedNat [0xffffa8a83f003f00,0xfbfafbfa0b0a0b0a,0xfafafffaff88ff88,0x5700570000ff0000,0xff00fcfffffafa,0xffcccccce4e4e4e4,0xfff0f0f000cc00cc,0xffcc0f0c33332222,0xff50ff5033003300,0xfaf0faf0eecceecc,0xe0c0e0c050505050,0xfeccfecc0f0f0000,0xbbbbaaaaafafaaaa,0xa000a0000ff00,0x2f2f22220f0f0a0a,0xabaaabaababababa]))
|0,7=>(OfNat.ofNat (packedNat [0xccccf0f0fcff0000,0x50555050cfcccfcc,0xafafaeae0c0e0c0e,0x30ba30ba32320000,0x5555444401010000,0x8f8f8888dcdcfcfc,0x5050f0f0fcfc5454,0xccffccfccdcdcccc,0xccaaccaaf8f8f8f8,0x8c0c8c0c50f050f0,0xf3f3f0f003030202,0xf0fff055505550,0xf3f2f3f211111010,0xffff030004040c0c,0x2020202f2f2f2f2,0xccc0ccc0c8fac8fa]))
|0,8=>(OfNat.ofNat (packedNat [0xfa00fa00,0xcccc11001100,0x50005000000ffcc,0xcceecceeff00aa00,0x55505050fffcfcfc,0x5400540055ff0000,0xcecececefffafafa,0xf0a0a0afcfefcfe,0x5757000032303230,0xf0c0c0cf0c0f0c0,0xab00ab0000300030,0xfcfc00fc73507350,0xfeaafeaa00eeeeee,0xffa8ffa8fff0ccc0]))
|_,_=>0
def stPool:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x100e80439050e06e,0x707028043605000,0x435050d004330b0,0x404160e0c80e311,0x80a8042f070185c0,0x7168b05616050a80,0xe25018a43016050a,0x4e070500c0e0e13,0x94481c050000407,0x1188804161082804,0x200507c041e0e80c,0x41c0d8680419070,0x1830170b0540e0e0,0x3050041305048220,0x7070401e07070280,0x40d050300e0b0500,0x80e090101c100703,0x140404018080200]))
|1=>(OfNat.ofNat (packedNat [0x701804630518804,0x43098004072f818,0xe431897804072e9,0x70041c2d8fc0e160,0xe16804072c828040,0x703160040a2b8a00,0x4072b01804062a84,0x8041c05150a60a29,0x1440407280189e07,0x500c0e4e0513404,0x7051300e430b004,0x96070500c0407251,0x2404070512004171,0x891c8c0722818040,0x7051100e43070180,0x40705108040a0190,0x45c07200fc0e3e1e,0x8f076070500c0e0e]))
|2=>(OfNat.ofNat (packedNat [0x708014020385814,0x7c0101c2c663d808,0xe0a3d18004070b0,0x28f27813858380a0,0x11dc380a1c01c800,0xa289d8220707080e,0xa02039d00c1c0101,0xc1461399c8d00d0e,0x28040e100288202,0x3887014701785838,0xa1481c861637828,0x4070b018dc02368,0x70146c1701c2c0a3,0x59a80e691f0f4760,0x7070801402038380,0xc121701c5a400500,0x8d067330700e4305,0xc0407329909e07]))
|3=>(OfNat.ofNat (packedNat [0x478080e8e100291a,0x160e029180245858,0x380a010701452000,0x4514160e028d4074,0x4870142e29858145,0x2011a110310e0082,0xc66329fc04074308,0x1407100290a8101,0x1c383f4213c0e0e,0x10028d42f0b07014,0x203a0c400a03858,0x1482409a80e69331,0x94041c0519400070,0xe0287c3c0101c140,0x34013c2c1c051488,0x6160e028fe023f03,0x4380a03858fa1c05,0x80e16009b09607]))
|4=>(OfNat.ofNat (packedNat [0xb070141f0385838,0xa519a80ea20e029,0x4207500701402038,0x28a4510127c2c1c0,0x50080e9e051800e9,0xd0b07014070b0707,0x46145058380a4080,0x80e164e210040705,0xd029b34034380a,0x101c60842e0080e,0x200526804070e0fc,0x4402070583804350,0x1d321c4c0080e8e4,0xb82804960b255280,0x20b07014930105c2,0xc154900922160e02,0x896070b018380734,0x8701490039a4380a]))
|5=>(OfNat.ofNat (packedNat [0x1002804075a02908,0x203829667303870,0x143c590080e45050,0xc04075885802072,0x1858380a0101c2c1,0xc578080e1c051900,0x4070b0195c020382,0x908490101c1c0614,0x8082c1c1001004ad,0x30981000256028c2,0x600387014ab1e008,0xe0e3181804070b1,0x9954070b02854a90,0x38589c0a1501c2c1,0xc540a40407189790,0x82e0385858a75301,0xc2ca5050082e9505,0x15c04a40e028e002]))
|6=>(OfNat.ofNat (packedNat [0xe0297c02038397a,0x1c050080e160e029,0x78020b8581428010,0x1c2c66580080e0e1,0x2902024401c2c6,0x60e008a6160e028a,0x40203858380a5d80,0x80e165d07014160e,0x28fea30101c400a,0x2c01c86163319486,0xb90b070140203839,0x700a0103840ad401,0x180e45100280e430,0x7080140e0b07014b,0x70390c2c0a420080,0xe1c1f9740e160e02,0x96c070b0704c2503,0x858380a5a8085e0e]))
|7=>(OfNat.ofNat (packedNat [0xb1995c0a0101c2c,0xcc6582822070b070,0x14510101c3820053,0x8d4070e02994be0,0x101d92160e028040,0x70b0f87ac8012582,0xe164a82804070b19,0x838c70101c2c1c63,0x2804070b0287c38,0x3858383a011a01a,0x1c0531404072b058,0x380a0101c2c1c053,0xc0407070c4cc2e0,0x101c2c0a290080e1,0x6008080e1c05308c,0x20385838c10500,0x82c1c05154240203,0x85838c01eafc0e16]))
|8=>(OfNat.ofNat (packedNat [0x680080e163335038,0x6a038c4380a5f009,0xa607070701402340,0x34380a1e8080e160,0x5209a4020b0715a6,0x4000958160e028c,0x26881c2c1c0500,0x80e0e0b330140203,0x87014611c0080e16,0x33071380203a38e8,0x1c0526c0e160e028,0xd8020f0382c1c0e8,0x832070b070142e0,0x3858580a011a02ca,0xe0e0280e160e029a,0xc80101cd21c0512,0x45c1729858380a01,0x33c2c1c053380407]))
|9=>(OfNat.ofNat (packedNat [0x50080e430b07014,0x207058380a6c9a8,0xe690e029562e038,0x5838c605008380a0,0xb80e530b0287c0,0x203b343820050080,0xe310e02904020b07,0x14386c0b80e450b,0x7014160e0296e02,0x38c438306709c0e,0xe0b070140203858,0xcc0a680080e160e0,0x29ae020b07040ad4,0x3580e160e0297c0,0x2560583820050080,0xecd0e028c06a6a81,0xc2c1c050090e160e,0x28fe0203858380a]))
|10=>(OfNat.ofNat (packedNat [0x3839c41c050b804,0x70b384140203858,0x38e00537c0e160e0,0x2804190b070144f0,0x3858380a30808d01,0x70b070140203858c,0xc0a42008d0160e02,0x8240203858380a42,0x82c1c053785202,0x31858380a40008f0,0x170b254140203b74,0x2c1c050080e160e0,0x29b80203b6c2c1c0,0x50382c1c05361880,0x203858380a09009b,0x4160e028d8020385,0x8380a2c01c1c160e,0x9452020f0594a1c]))
|11=>(OfNat.ofNat (packedNat [0xe02804d503858cc,0xa010382c1c051fc,0x40718858383d038,0x58cc1c0528c04070,0xb07014ea010780e0,0xe1002804070b2b81,0x43e011a02c1c053a,0x404072f858380a01,0x1c1c16332480407,0x7114400a011a01a,0x1c053a004070b330,0x14600101dce160e0,0x2804070b070148c0,0x101c2c1c05399ca0,0x70b0701402038583,0x8b8050082c1c0504,0x9880203859980a39,0x8080e740e029c802]))
|12=>(OfNat.ofNat (packedNat [0x3bc82c1c050080e,0x1678870140234034,0xcc1c050080e1c053,0x28920207058380a2,0x8080e1678070140,0x217858380a010583,0x80a6f20004070b02,0x87cd0010782c1c77,0x8285c070b1001430,0x101ddc1c051b004,0x70b0297c841701c,0x2c40053287607070,0x58380a1701c2c400,0x51451a5307058380,0xa0f058380a360500,0x47829858380a0105,0x8380a568e004070e,0x29daec0101c1ceb]))
|13=>(OfNat.ofNat (packedNat [0xe02804070b07014,0xfd0107968160e028,0x4070b199f80a010,0x1c2c663024804070,0xb071f60a0101d681,0xc0532804070b0701,0x4fa0390c2c660e02,0x804070b07014f901,0x1c2c1c053e00407,0x5a058380a2581c1c,0x160e0280e160e029,0xeec80881c2c1c052,0x1404070b2b814610,0x101c2c1c053d8040,0x70707014380101c2,0xc1c053d404074385,0x838b003858380a51,0x8080ef40e029e602]))
|14=>(OfNat.ofNat (packedNat [0x101c2c1c0542404,0x170b4212a0a0101c,0x2c1c8382804170b2,0x5415060101c1c163,0x32c0040782858380,0xa1701c2c1c053080,0x40705184c0290101,0xc2c1c05410040743,0x858389c0101e0616,0xe02804780385838,0xa0390c2c1c05008,0xe160e02a0402808,0x382c1c050080e870,0xb07014028001c2c1,0xc0513c0e0e0b0701,0x40203838400a0e9a,0x80e167f870140203,0xa0c2c1c0501dfc16]))
|15=>(OfNat.ofNat (packedNat [0xb0701402038382c,0xa423940e0e0b070,0x14020385838c6490,0x80e0e1899814070,0x7058380a880080e1,0x687828c0023c01c1,0xc20050080e0e1002,0x95a02038382c664e,0xa1c070b0701402,0x38c438304213c0e,0x160e0801402038c4,0x2c6642008f0160e0,0x28240203858380a8,0x69a910070b070140,0x203a1c2c0a420080,0xf0c0b07014070b07,0x150b0101c2c1c05,0x42804070e028c249]))
|16=>(OfNat.ofNat (packedNat [0xb070146a0385838,0xa5f0080e160e028,0xc0920101c1c160e0,0x28520203858389c7,0x19180e450b070140,0x7218382c1c0501df,0xc0e0b07014020385,0x8380a898080e1605,0x210b802038580c1c,0x149a82e530b07014,0x28901c2c1c05008,0xe160e0293802038,0x38620a420080ebd0,0xe028c202038595c2,0x501d0e430b0701,0x46a0394c621c0500,0x80e160e02a220203,0x838400a148080ee2]))
|17=>(OfNat.ofNat (packedNat [0xb0701484230080e,0xe0b070140203858,0x380a092340407070,0x58380a0101c2d150,0xe02805140b070146,0xa0101c1c160e0280,0x4070b198380a360b,0x804070b070146101,0x1c1c160e0296002,0x38c42c660e02804,0x70b07014d00881c,0x2c1c052f804070e0,0x29d80203858380a4,0x10080e1633070140,0x2038595c1c050080,0xe160e31814020383,0x82c1c05094040707,0x58380a3a8080e45]))
|18=>(OfNat.ofNat (packedNat [0xe028aa020394c1c,0x160e028040707058,0x380a1e8b80e16200,0x28040707058380a4,0x808d0070b070151,0x9013540e160e0280,0x40707058380a4e00,0x80e310b0707a0203,0x858cc1c054600407,0x18858380a4204404,0x707058380a03858,0x380a880080e160e0,0x2a2e0203858380a1,0x82f804070b070400,0xa148080e160e0299,0x4be03858380a0a00,0x80e160e028c02901,0x1c2c1c054580407]))
|19=>(OfNat.ofNat (packedNat [0x52c0040707058cc,0xa010782c1c0e808,0xe318d058380a350,0x8d0070b07014020,0x38382c1c05310040,0x78d058380a0101c1,0xc450b070140203b3,0x4380a0101c621633,0x70040766858380a,0x105838ad4000958,0x160e02804070b070,0x14be49008f0070b0,0x70140203a1c2c1c0,0x50080e160e0290a0,0x2038382c1c0538c0,0x4070b0f87a0203a1,0xc2c660e02804075a,0x58380a0101c1c16]))
|20=>(OfNat.ofNat (packedNat [0x7058380a0101c2c,0x1c050a404070b070,0x14ad0101c2c1c052,0x4804070b070141d0,0x101c2c1c052f8040,0x70b0701402038583,0x80a620080e163307,0x14020f01c2c1c05,0x8d0070b0701402,0x3858380a718080e,0x8707058380a4694c,0x2c1c050080e160e0,0x2938020394c2c660,0xe028048803858380,0xa0101dc4160e028d,0x40729858380a3500,0x82e070b07014160e,0x29b0c40101c2c1c]))
|21=>(OfNat.ofNat (packedNat [0x80e160e02,0x8040729858380a46,0x8080e160e0280407]))
|_=>0
def stOffB:Nat → Nat → Nat
|2,0=>(OfNat.ofNat (packedNat [0xf300c3,0x93006300330003]))
|3,0=>(OfNat.ofNat (packedNat [0x10641024,0xfe40fa40f640f24,0xee40ea40e640e24,0xde40da40d640d24,0xce40ca40c640c24,0xbe40ba40b640b24,0xae40aa40a640a24,0x9e409a409640924,0x8e408a408640824,0x7e407a407640724,0x6e406a406640624,0x5e405a405640524,0x4e404a404640424,0x3e403a403640324,0x2e402a402640224,0x1e401a401640124]))
|4,0=>(OfNat.ofNat (packedNat [0x2455240523b52365,0x231522c522752225,0x21d52185213520e5,0x209520451ff51fa5,0x1f551f051eb51e65,0x1e151dc51d751d25,0x1cd51c851c351be5,0x1b951b451af51aa5,0x1a551a0519b51965,0x191518c518751825,0x17d51785173516e5,0x1695164515f515a5,0x1555150514b51465,0x141513c513751325,0x12d51285123511e5,0x1195114510f510a5]))
|4,1=>(OfNat.ofNat (packedNat [0x344533f533a5,0x3355330532b53265,0x321531c531753125,0x30d5308530352fe5,0x2f952f452ef52ea5,0x2e552e052db52d65,0x2d152cc52c752c25,0x2bd52b852b352ae5,0x2a952a4529f529a5,0x2955290528b52865,0x281527c527752725,0x26d52685263525e5,0x2595254524f524a5]))
|5,0=>(OfNat.ofNat (packedNat [0x4bb64b564af64a96,0x4a3649d649764916,0x48b6485647f64796,0x473646d646764616,0x45b6455644f64496,0x443643d643764316,0x42b64256420541a6,0x414640e640864026,0x3fc63f663f063ea6,0x3e463de63d863d26,0x3cc63c663c063bc4,0x3b663b063aa63a55,0x39f639b4395638f6,0x3896383637d63776,0x371636c536753616,0x35b6355634f63496]))
|5,1=>(OfNat.ofNat (packedNat [0x634662e662866226,0x61c66166610660a6,0x60465fe65f865f26,0x5ec65e665e065da6,0x5d465ce65c865c26,0x5bc65b665b065aa6,0x5a4659e659955936,0x58d65876581657b6,0x575656f656a55655,0x55f65596553654d6,0x5476541653b65356,0x52f65296523651d6,0x5176511650b65056,0x4ff64f964f364ed6,0x4e764e344dd64d76,0x4d164cb64c564c14]))
|5,2=>(OfNat.ofNat (packedNat [0x7af67a967a3679d6,0x7976791678c57866,0x780677a6774676e6,0x7686762675c67566,0x750674a6744673e6,0x7386733572d67276,0x721671b6715670f6,0x709670366fe56f86,0x6f266ec66e666e06,0x6da66d466ce66c86,0x6c266bc66b666b06,0x6aa66a4669e66986,0x692668c668756816,0x67b6675666f66696,0x663665d665856526,0x64c66466640663a6]))
|5,3=>(OfNat.ofNat (packedNat [0x863685d6,0x8576851684b68456,0x83f68396833682d6,0x8276821681b68156,0x80f6809680367fd6,0x7f767f167eb67e56,0x7df67d967d367cd6,0x7c767c167bb67b56]))
|6,0=>(OfNat.ofNat (packedNat [0x9f869f359ec79e57,0x9de79d869d179cc5,0x9c669c069bb59b65,0x9af79a969a3699d6,0x9967991598a79846,0x97d7976796f796a5,0x963795c7956694f7,0x9496942793b79347,0x92f59296922791b7,0x914790f590879026,0x8fc68f578ef68e87,0x8e268dd58d678cf7,0x8c878c178ba78b46,0x8ae68a958a3689d6,0x8976891688a78837,0x87d6877687078697]))
|6,1=>(OfNat.ofNat (packedNat [0xa3b6a347a2f5,0xa296a227a1c6a166,0xa106a097a0459fe6]))
|7,0=>(OfNat.ofNat (packedNat [0xa886,0xa826a7c6a766a706,0xa6a6a646a5e6a595,0xa536a4d6a476a416]))
|8,0=>0xa8e5
|_,_=>0
def wireSAt (i:Nat):Nat:=if i < 283 then fld (dictB (i / 512) (i / 32 % 16)) 32 (i % 32) else 0
def readSt:Nat → Nat → List Nat
|0,_=>[]
|n+1,p=>wireSAt (fld (stPool (p / 128)) 9 (p % 128))::readSt n (p+1)
def SS (s j:Nat):List Nat:=let v:=fld (stOffB s (j / 64)) 16 (j % 64);readSt (v &&& 15) (v >>> 4)
def SD (s j:Nat):List (Nat × Nat × Nat):=(SS s j).map (fun w=>(w,projBit r1sG w,projBit r2sG w))
def htAt (s i:Nat):Nat:=fld (HT s (i / 128)) 32 (i % 128)
def idxH (s h:Nat):Nat:=bsr (htAt s) h 9 0 (NN s)
def idx (s:Nat) (zs:List Nat):Nat:=idxH s (hk 0 zs)
def opPool:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0xe3110101e0b0290,0xb0710e029038710b,0x2b0383a0383b0b0,0x710b02a0b0710382,0xa038580e02907028,0xb071298290101c0,0xe029038710b2ba03,0x82a4694f0101c010,0x1d0e02a0b0700e00,0x20b00543ac307029,0x70280b070170280,0x3871038380e0032a,0x8490383a0383b0b0,0x710f073038290b00,0x401075038280b071,0xb0710b029298290,0x3a1e0b1990b02803,0x82a0b02801075038,0x280f073038290b19,0xa0383a0e00003871]))
|1=>(OfNat.ofNat (packedNat [0x382903873038714,0x38730b1990e02901,0x3a038710b070010,0x1f0101e0b0710387,0x3038280e31103ac3,0x702817028038710,0x38710b0700e07503,0x8280387103838469,0x4f0101c0101d0387,0x30b0710f07303829,0xb0710b070350290,0xb0700b0722987101,0x1c0b02a0101c038,0x71038710b0710382,0x834073038714382b,0xb1990e029668710,0x3858038590101c0e,0x290e31166870038,0x28039980e0290387,0x30b029052f903873]))
|2=>(OfNat.ofNat (packedNat [0xb0710b029038730,0xe0290e02a038710b,0x19a0b0710b0710b0,0x730b1990b0713407,0x303871182f90b028,0x387307029070280,0xe077038280b0290e,0x2b0e0290b071038,0x2a038290b0280385,0x80b0280101c0b071,0x101d0b0710e0770,0x38280b2f9038730e,0x292987103a1e070,0x290e029038290b07,0x10e029038710e075,0x38280f073038290,0xb0710b0710382a0b,0x710e38d0702a0b0,0x710b858331b30385,0xb0b0710b07101078]))
|3=>(OfNat.ofNat (packedNat [0x38730b0710b0710,0x3828038380b07103,0x873038710e02a0b0,0x710382a0702b0702,0xa011570383b01071,0xb19a0e0290b0700,0xb0290382a0e02901,0x1550383b0b071038,0x730b0290b0710e02,0x901077038280e249,0xe02a038390382b0,0x702b0b0716a82901,0x1c0e02901078038,0x290b19a0103a0383,0x9298290e0290b071,0x668730e02903a730,0x702b07028073130b,0x710101e05271070,0x2b0b07103ac10702,0x80b0710b07103828]))
|4=>(OfNat.ofNat (packedNat [0x101c0e02a038580,0xb071010722987101,0x1c0702b0b0710b0,0x2a0e0290399b0e02,0x90b19a0e0290b071,0x1077038280399b0,0xe0290b028038730b,0x700382a0b02b038,0x730107a038290b07,0x20382a011a203871,0xb19a0e0290b0710,0x383a0b0710b07101,0x1d0e0a50382a010,0x78038290b0710387,0x10385b0e02903871,0x70280b0710b0290,0xe0290f0730382903,0x873038290e077038,0x2834073038710e02,0xa0e3110101e052f9]))
|5=>(OfNat.ofNat (packedNat [0x3828038730101e0,0xe029038290387107,0x2a0b071070290b0,0x710101c0101d0702,0xb0b0710101c0e029,0x298290101c0e2490,0xe02a0101c0387101,0x71038710101f010,0x1e070280b0710b07,0x10e0290382803829,0xe02901059038710,0xb0710101e039980e,0x290b0710b0290e0,0x290e075038280102,0xb01075038280b02a,0x3873038390b0710,0xb1990e0290b07107,0x2a0b0710b02b0b1,0x990e0290b2f90387,0x30383b0b0710b071]))
|6=>(OfNat.ofNat (packedNat [0x101c0101,0xd0382a0382b0e02a]))
|_=>0
def opOffB:Nat → Nat → Nat
|3,0=>(OfNat.ofNat (packedNat [0x100000000000,0x0,0x0,0x0,0x0]))
|4,0=>(OfNat.ofNat (packedNat [0x142098,0x8000000000000000,0x89000000,0x8080000000f,0x100000001a40b200,0x0,0x5080001,0x2200000002040000,0x3100000000000,0x0,0x0,0x2100c4000,0x84000000]))
|4,1=>(OfNat.ofNat (packedNat [0xa4400000,0x98c00025100,0x90400000000000,0x46200011080003,0xe600000000000001,0xe100000003841b10,0x3420000000,0x5cc,0x0,0x2c2000]))
|5,0=>(OfNat.ofNat (packedNat [0x3189884c045f12f0,0x9744b825b12c9000,0x58100015c4ac,0x20000000000aa253,0x2289138c9a200000,0x98200000000,0x94400024111880,0x11088620,0x20180000000000,0xf880003b31d08,0xe440000001b18000,0x6a23320000c845e6,0x1618ac4542000]))
|5,1=>(OfNat.ofNat (packedNat [0x4f9,0x80013c20004e1268,0x93049624a8800000,0x941000000126292,0x100024451e48d246,0x80011628a144880,0x863428a0c90,0x428113f91f48f467,0x820001dc40000000,0x7523a09,0xcc4e420003888000,0xde46d20001b04000,0x6933408000ce2643]))
|5,2=>(OfNat.ofNat (packedNat [0x6a8b4c8000d21688,0xb404000cf1670800,0xcc200032c590,0x600000000018c4c5,0x10000000000c3261,0x8001822c010002f,0xc40000000002f497,0x64ba100000000000,0x5c880017020005,0xb8ad856a2b23579a,0xb48000ab20000001,0x542a8200000014e2,0xa615288001464a21]))
|5,3=>(OfNat.ofNat (packedNat [0x1e,0x640000003c480000,0x3c040000007,0x710001da20007608,0x1d62000750b9cd,0xcc2e3370937c9bc2,0xdd16d93649b02d62]))
|6,0=>(OfNat.ofNat (packedNat [0xb11580abe35d2ad9,0x564ab02000ab1550,0xaa63512a79534a96,0x54a1a4151c68a543,0x2a094fca7c33d19e,0xcec67253729a94c,0xca6253019714b0a5,0x45282931490a4452,0x28f147463651928,0xb9454a265112880c,0x38a1850a2841418a,0x850318093fc9fc2,0xfc27d13e09ee2f52]))
|6,1=>(OfNat.ofNat (packedNat [0x5e0a,0xec5742b915c0adc5,0x6c2b515a0acc5642]))
|7,0=>(OfNat.ofNat (packedNat [0x1841c188003,0x43811c00dfc6fc2,0xbe8df06f637a1]))
|_,_=>0
def readOps:Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
|n+1,p=>let code:=fld (opPool (p / 64)) 20 (p % 64);(code &&& 3,wireSAt ((code >>> 2) &&& 511),wireSAt ((code >>> 11) &&& 511))::readOps n (p+1)
def PO (s j:Nat):List (Nat × Nat × Nat):=let v:=fld (opOffB s (j / 64)) 13 (j % 64);readOps (v &&& 15) (v >>> 4)
def pmPalB:Nat → Nat
|0=>(OfNat.ofNat (packedNat [0x1003b0e0300ac290,0xa027098250902208,0x4200681805012044,0x100380c02c0a0240,0x80180400c0200400]))
|1=>(OfNat.ofNat (packedNat [0x3ace933cc9320c02,0xb4ac2a0a7298a528,0x4a02388721081200,0x7b1e4721a8631685,0x2144501204310841]))
|2=>(OfNat.ofNat (packedNat [0xdef59c7effbf6f7b,0x32498e219806007f,0x5f97a5e76617b59d,0x6658d61581425013,0xb46510400ff3ecec]))
|3=>0x3fbfdff5fc77f
|_=>0
def pmB:Nat → Nat → Nat
|3,0=>(OfNat.ofNat (packedNat [0x200000000,0x0,0x0]))
|4,0=>(OfNat.ofNat (packedNat [0x4,0x4001001000,0x3000a000800,0xb0000381000,0x300000000200040,0x300,0x80010a0000018,0x2000000c00,0x60001312000000,0x10000800,0x300020200000000,0x200000,0x2080000004002]))
|5,0=>(OfNat.ofNat (packedNat [0x8a3060002,0x4e40102000010090,0xf8100340818e0118,0x10c0002e24496820,0x24c981001800c180,0x2a01180498086000,0x87002413d5e0091b,0x240a8c626589f02,0x3200481800002,0xa22024c5020000c8,0xe0011000000,0x8020c340000b188,0x36885c0000e483,0x1500719809950300]))
|5,1=>(OfNat.ofNat (packedNat [0x800,0x40000030000260,0x300220008002800,0xb302040816524081,0x6404011023c01f02,0x613184aa800000,0xa300000010a0080,0x10c300000ce89840,0x5a01080101,0x810d2c0400100007,0x100003012490c94]))
|6,0=>(OfNat.ofNat (packedNat [0xd97,0x463132863bb5e5b6,0x6cad35eb0fc33b6c,0xf9dcf6e78c275cd4,0x9d24b289990c765b,0x36ca9984a2a4d303,0x5699643018f56b76,0x4d2826cd9c270f31,0x138d4c53958689b4]))
|7,0=>(OfNat.ofNat (packedNat [0x4dbe4ee,0x416cfa761c0da12c]))
|8,0=>0x13
|_,_=>0
def PM (s j:Nat):Nat:=let k:=fld (pmB s (j / 128)) 7 (j % 128);fld (pmPalB (k / 32)) 10 (k % 32)
def mkPools (s i:Nat):List (Nat × Nat × (Nat × List Nat)):=
  let pm:=PM s i
  if pm==0 then [] else
    let ops:=PO s i
    (if pm.testBit 0 then [(dom_27,6,runOps true dom_27 (0,roots_27) ops)] else [])++(if pm.testBit 1 then [(dzo_22_8,4,runOps true dzo_22_8 (0,roots_22) ops)] else [])++(if pm.testBit 2 then [(dzo_14_16,4,runOps true dzo_14_16 (0,roots_14) ops)] else [])++(if pm.testBit 3 then [(dom_7,4,runOps true dom_7 (0,roots_7) ops)] else [])++(if pm.testBit 4 then [(dzo_23_8,5,runOps true dzo_23_8 (0,roots_23) ops)] else [])++(if pm.testBit 5 then [(dom_29,6,runOps true dom_29 (0,roots_29) ops)] else [])++(if pm.testBit 6 then [(dom_23,5,runOps true dom_23 (0,roots_23) ops)] else [])++(if pm.testBit 7 then [(dom_30,5,runOps true dom_30 (0,roots_30) ops)] else [])++(if pm.testBit 8 then [(dom_15,5,runOps true dom_15 (0,roots_15) ops)] else [])++(if pm.testBit 9 then [(dzo_15_16,5,runOps true dzo_15_16 (0,roots_15) ops)] else [])
def mkCut (s i:Nat) (g:Nat × Nat × Nat) (zs:List Nat):Bool:=(mkPools s i).any fun e=>checkPool true e.1 e.2.1 (s-1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h:mkCut (s+1) i g ys=true):¬ RunD true dom_31 goalM s ys:=by
  unfold mkCut mkPools at h;dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e,he,hchk⟩:=h
    simp only [List.mem_append,List.mem_ite_nil_right,List.mem_singleton,or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) lowS_27_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_22_40_8 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_14_48_16 _ g hchk
    · exact cpcs (by decide +kernel) lowS_7_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_23_40_8 _ g hchk
    · exact cpcs (by decide +kernel) lowS_29_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_23_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_30_32 _ g hchk
    · exact cpcs (by decide +kernel) lowS_15_32 _ g hchk
    · exact cpcs (by decide +kernel) lowSh_15_48_16 _ g hchk
def cutRoot (s:Nat) (ws:List Nat):Bool:=checkPool true dom_27 6 s (0,roots_27) ws
theorem cutRoot_sound {v ys} (h:cutRoot v ys=true):¬ RunD true dom_31 goalM v ys:=by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) lowS_27_32 h
def symsG:List (List (Nat × Nat)):=[[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8)],[((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2)],[((OfNat.ofNat (packedNat [0xff000000ff00,0xff000000ff00,0xff000000ff00,0xff000000ff00])),8),((OfNat.ofNat (packedNat [0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0c])),2)]]
theorem symsG_ok:symsG.all (fun ms=>ms.all moveOK256 && (applyMoves ms dom_31==dom_31) && (applyMoves ms goalM==goalM))=true:=by decide +kernel
def ori (zs:List Nat):List Nat:=pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h:RunD true dom_31 goalM v ys):RunD true dom_31 goalM v (ori ys):=pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s:Nat):=barP true dom_31 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
private theorem z0:∀ i,0 ≤ i → i < 0 → Z 0 i=true:=by omega
private theorem z1:∀ i,0 ≤ i → i < 0 → Z 1 i=true:=by omega
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z2:∀ i,0 ≤ i → i < 6 → Z 2 i=true:=span_ok (by decide +kernel:span (Z 2) 6 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z3:∀ i,0 ≤ i → i < 62 → Z 3 i=true:=span_ok (by decide +kernel:span (Z 3) 62 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z4:∀ i,0 ≤ i → i < 115 → Z 4 i=true:=span_ok (by decide +kernel:span (Z 4) 115 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_0:∀ i,0 ≤ i → i < 128 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 128 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z5_128:∀ i,128 ≤ i → i < 222 → Z 5 i=true:=span_ok (by decide +kernel:span (Z 5) 94 128=true)
private theorem z5:∀ i,0 ≤ i → i < 222 → Z 5 i=true:=(range_split z5_0 z5_128)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z6:∀ i,0 ≤ i → i < 75 → Z 6 i=true:=span_ok (by decide +kernel:span (Z 6) 75 0=true)
set_option maxRecDepth 40000 in set_option maxHeartbeats 0 in private theorem z7:∀ i,0 ≤ i → i < 13 → Z 7 i=true:=span_ok (by decide +kernel:span (Z 7) 13 0=true)
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
end S_31_32
theorem lowS_31_32:Lower true dom_31 roots_31 goal_31_32 9:=S_31_32.noCircuit
end Case1
open Logic Search
def obs (d : Nat) (e : Nat → Fin 6 → Bool) (f : BF 6) := (tt 64 e f) &&& d
theorem obs_op (d : Nat) (e : Nat → Fin 6 → Bool) (a b : BF 6) :
    obs d e (fAnd a b) = opD d 0 (obs d e a) (obs d e b) ∧
    obs d e (fOr a b) = opD d 1 (obs d e a) (obs d e b) ∧
    obs d e (fDiff a b) = opD d 2 (obs d e a) (obs d e b) := by
  have zero (u v : Nat) : opD d 0 u v = (u &&& v) &&& d := rfl
  have one (u v : Nat) : opD d 1 u v = (u ||| v) &&& d := rfl
  have two (u v : Nat) : opD d 2 u v = (u &&& ((v ^^^ mask256) &&& d)) &&& d := rfl
  simp only [zero,one,two]
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [obs,opD,andD,orD,negD,tt_testBit,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
      fAnd,fOr,fDiff,fBin,bDiff,mask256,Nat.testBit_two_pow_sub_one] <;>
    by_cases h : i < 64 <;> by_cases h' : i < 256 <;>
    cases ha : a (e i) <;> cases hb : b (e i) <;> cases hd : d.testBit i <;>
    simp_all <;> omega

theorem simulate (d : Nat) (e : Nat → Fin 6 → Bool) (roots : List Nat) (f : BF 6) :
    ∀ k (L : List (BF 6)) n bank, NatReach true d roots n bank →
      (∀ x ∈ L, Avail true d bank (obs d e x)) → R f k L →
      ∃ q B, q ≤ n+k ∧ NatReach true d roots q B ∧ Avail true d B (obs d e f) := by
  intro k
  induction k with
  | zero =>
    intro L n B hr hsup h
    exact ⟨n,B,by omega,hr,hsup f h⟩
  | succ k ih =>
    intro L n B hr hsup h
    rcases h with hm | ⟨s,⟨a,ha,b,hb,hop⟩,next⟩
    · exact ⟨n,B,by omega,hr,hsup f hm⟩
    have build (op : Nat) (ok : allowedB true op=true)
        (eq : obs d e s=opD d op (obs d e a) (obs d e b)) :
        NatReach true d roots (n+1) (obs d e s :: B) := by
      exact ⟨B,obs d e a,obs d e b,op,ok,by rw [eq],hr,hsup a ha,hsup b hb⟩
    have newB : NatReach true d roots (n+1) (obs d e s :: B) := by
      rcases hop with rfl | rfl | rfl
      · exact build 0 (by decide) (obs_op d e a b).1
      · exact build 1 (by decide) (obs_op d e a b).2.1
      · exact build 2 (by decide) (obs_op d e a b).2.2
    obtain ⟨q,T,le,reach,hit⟩ := ih (s::L) (n+1) _ newB (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr (Or.inl ⟨_,List.mem_cons_self,rfl⟩)
      · exact avail_cons _ _ (hsup x hx)) next
    exact ⟨q,T,by omega,reach,hit⟩

theorem observedFloor (d : Nat) (e : Nat → Fin 6 → Bool) (f : BF 6) (roots : List Nat) (T lb : Nat)
    (sup : (L0 6).all (fun x => availB true d roots (obs d e x))=true)
    (eq : obs d e f &&& d = T &&& d) (lower : Lower true d roots T lb) :
    ∀ k, R f k (L0 6) → lb ≤ k := by
  intro k h
  obtain ⟨q,B,le,hr,hit⟩ := simulate d e roots f k (L0 6) 0 roots rfl
    (fun a ha => (availB_iff ..).mp (List.all_eq_true.mp sup a ha)) h
  exact le_trans (lower q B hr (avail_of_eq eq hit)) (by omega)

theorem observedFloorDual (d : Nat) (e : Nat → Fin 6 → Bool) (f : BF 6) (roots : List Nat) (T lb : Nat)
    (sup : (L0 6).all (fun x => availB true d roots (obs d e x))=true)
    (eq : negD d (obs d e f) &&& d = T &&& d) (hmask : d &&& mask256 = d)
    (lower : Lower true d roots T lb) : ∀ k, R f k (L0 6) → lb ≤ k := by
  intro k h
  obtain ⟨q,B,le,hr,hit⟩ := simulate d e roots f k (L0 6) 0 roots rfl
    (fun a ha => (availB_iff ..).mp (List.all_eq_true.mp sup a ha)) h
  exact le_trans (lower q B hr (avail_of_eq eq (avail_neg hmask hit))) (by omega)

open Logic Search

open Logic Search
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def posted : BF 6 := fun x => Nat.testBit (4276677312 * 2 ^ 32 + 3938510976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def tab : BF 6 := fun x => Nat.testBit 18368189194523699328 (Nat.ofBits x)
theorem targetEq : posted = tab := funext (all_pts _ (by decide +kernel))
def sample0 (k : Nat) : Fin 6 → Bool := fun i => !k.testBit (([99, 0, 1, 2, 3, 4] : List Nat).getD i.val 99)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem restricted0 : ∀ k, R (phi (0 : Fin 6) false (nz tab)) k (L0 6) → 9 ≤ k :=
  observedFloorDual Case0.dom_31 sample0 _ Case0.roots_31 Case0.goal_31_32 9 (by decide +kernel) (by decide +kernel) (by decide +kernel) Case0.lowS_31_32
def sample1 (k : Nat) : Fin 6 → Bool := fun i => k.testBit (([99, 1, 2, 0, 3, 4] : List Nat).getD i.val 99)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem restricted1 : ∀ k, R (phi (0 : Fin 6) true (nz tab)) k (L0 6) → 9 ≤ k :=
  observedFloor Case1.dom_31 sample1 _ Case1.roots_31 Case1.goal_31_32 9 (by decide +kernel) (by decide +kernel) Case1.lowS_31_32
theorem gateBound : ∀ k, R (nz tab) k (L0 6) → 11 ≤ k := by
  intro k h
  obtain ⟨q,rfl,hq | hq⟩ := two_gates (0 : Fin 6) (nz tab) (ne_F _ (pt 14) (by decide +kernel)) (ne_F _ (pt 6) (by decide +kernel)) (reads (0 : Fin 6) _ (pt 6) (by decide +kernel)) k (L0 6) (good_L0 _) h
  · have := restricted0 q hq
    omega
  · have := restricted1 q hq
    omega
def witness : List Gate := [⟨.and,[3,0]⟩,⟨.or,[0,3]⟩,⟨.and,[1,2]⟩,⟨.or,[8,6]⟩,⟨.or,[1,2]⟩,⟨.and,[10,7]⟩,⟨.or,[11,5]⟩,⟨.and,[12,9]⟩,⟨.and,[11,5]⟩,⟨.or,[14,9]⟩,⟨.and,[4,15]⟩,⟨.or,[13,16]⟩]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witOK : ∀ x : Fin 6 → Bool, Circuit.eval ⟨witness,17⟩ (List.ofFn x) = posted x := by
  rw [targetEq]
  exact all_pts _ (by decide +kernel)
end PEqualNP.Outside.L_meta_49149_aux
open PEqualNP.Outside.L_meta_49149_aux PEqualNP.Outside.L_meta_49149_aux.Logic in
theorem PEqualNP.Outside.L_meta_49149 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677312 * 2 ^ 32 + 3938510976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677312 * 2 ^ 32 + 3938510976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  apply mono_shape2 posted 11 _ witness 17 (monoOK_sound _ (by decide +kernel)) (by decide +kernel) witOK
  rw [targetEq]
  exact gateBound
