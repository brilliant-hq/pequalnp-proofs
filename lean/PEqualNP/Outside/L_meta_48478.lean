import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_48478
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 128
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
lemma bin_comm_flip (d : Nat) (hd : d < 4) (a b : Nat) : bin d a b = bin (flipOp d) b a := by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
lemma flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  interval_cases d <;> decide
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^128) (hb : b < 2^128) : bin d a b < 2^128 := by
  have h1 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x &&& y) < 2^128 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ||| y) < 2^128 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ^^^ y) < 2^128 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
lemma bin_bit0 (d a b : Nat) (ha : a.testBit 0 = false) (hb : b.testBit 0 = false) :
    (bin d a b).testBit 0 = false := by
  rw [testBit_bin]
  rcases d with _ | _ | _ | d <;> simp [ha, hb]
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_size {T k S} (h : Live T k S) : S.card ≤ k + 1 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; simp
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, hf, tail⟩ := h
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have ht := ih tail
    rw [Finset.card_insert_of_notMem hu] at ht
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def swZero : SWire := (false, 0)
def swFlip (a : SWire) : SWire := (!a.1, a.2)
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def swMeet (a b : SWire) : SWire := (a.1 && b.1, bin (opIdx a.1 b.1) a.2 b.2)
def swJoin (a b : SWire) : SWire := swFlip (swMeet (swFlip a) (swFlip b))
def swRead (j : Nat) (a : SWire) : Bool := a.1 != a.2.testBit j
lemma swRead_zero (j : Nat) : swRead j swZero = false := by simp [swRead, swZero]
lemma swRead_flip (j : Nat) (a : SWire) : swRead j (swFlip a) = !(swRead j a) := by
  cases a with | mk s v => cases s <;> cases h : v.testBit j <;> simp [swRead, swFlip, h]
lemma swRead_meet (j : Nat) (a b : SWire) : swRead j (swMeet a b) = (swRead j a && swRead j b) := by
  obtain ⟨s, u⟩ := a; obtain ⟨t, v⟩ := b
  cases s <;> cases t <;> cases hu : u.testBit j <;> cases hv : v.testBit j <;>
    simp [swRead, swMeet, opIdx, testBit_bin, hu, hv]
lemma swRead_join (j : Nat) (a b : SWire) : swRead j (swJoin a b) = (swRead j a || swRead j b) := by
  simp only [swJoin, swRead_flip, swRead_meet]
  cases swRead j a <;> cases swRead j b <;> rfl
def swGate (w : List SWire) (g : Gate) : SWire :=
  let arg := fun i => w.getD i swZero
  match g.op, g.inputs with
  | .not, xs => swFlip (arg (xs.headD w.length))
  | .and, [] => swFlip swZero
  | .or, [] => swZero
  | .and, [i] | .or, [i] => arg i
  | .and, i :: j :: _ => swMeet (arg i) (arg j)
  | .or, i :: j :: _ => swJoin (arg i) (arg j)
  | _, _ => swZero
def swExec (gs : List Gate) (w : List SWire) : List SWire :=
  gs.foldl (fun w g => w ++ [swGate w g]) w
def isBin (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma get_simple (w : List SWire) (i : Nat) : simple w (w.getD i swZero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
lemma swGate_priced (w : List SWire) (g : Gate) : priced w (isBin g) (swGate w g).2 := by
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | not => exact Or.inl (get_simple w _)
  | _ => exact Or.inl (Or.inl rfl)
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^128 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^128 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^128 ∧ (w.getD i swZero).2.testBit 0 = false := by
    simp only [List.getD_eq_getElem?_getD]
    cases eq : w[i]? with
    | none => exact hz
    | some a => exact hw a (List.mem_of_getElem? eq)
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | not => exact hg (xs.headD w.length)
  | _ => exact hz
lemma swExec_lt (gs : List Gate) (w : List SWire)
    (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hw u hu
    · rw [List.mem_singleton.mp hu]; exact swGate_lt w hw g
lemma swRead_get (j : Nat) (w : List SWire) (i : Nat) :
    (w.map (swRead j)).getD i false = swRead j (w.getD i swZero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [swRead_zero]
lemma swGate_read (w : List SWire) (g : Gate)
    (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (j : Nat) :
    swRead j (swGate w g) = g.op.eval (g.inputs.map fun i => (w.map (swRead j)).getD i false) := by
  simp_rw [swRead_get]
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := legal
  rcases hop with rfl | rfl | rfl <;>
    rcases xs with _ | ⟨i, _ | ⟨k, _ | ⟨h, rest⟩⟩⟩ <;>
    simp_all [swGate, GateOp.eval, swRead_flip, swRead_meet, swRead_join, swRead_zero]
lemma swExec_read (j : Nat) (gs : List Gate) (w : List SWire)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (swExec gs w).map (swRead j) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (swRead j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (swExec gs (w ++ [swGate w g])).map (swRead j) = _
    rw [ih _ (fun v hv => legal v (List.mem_cons_of_mem _ hv))]
    simp [swGate_read w g (legal g List.mem_cons_self) j]
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
lemma extract_live {T} (hT : T ≠ 0) (gs : List Gate) (w : List SWire)
    (found : T ∈ reps (swExec gs w)) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {T}, by simp, ⟨rfl, hT⟩, by simpa [swExec] using found⟩
  | cons g gs ih =>
    obtain ⟨k, S, lim, h, sub⟩ := ih (w ++ [swGate w g]) found
    have sub' : ∀ a ∈ S, a ∈ reps w ++ [(swGate w g).2] := by simpa [reps] using sub
    obtain ⟨l, V, cost, hl, raw⟩ := pull_live h (swGate_priced w g) sub'
    refine ⟨l, V, ?_, hl, raw⟩
    rw [List.countP_cons]
    cases e : isBin g <;> simp [e] at cost ⊢ <;> omega
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 128 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 128 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^128) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Impossible (T : Nat) (cap : Nat) (S : Finset Nat) : Prop :=
  ∀ k ≤ cap, ¬Live T k S
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma lower_of_impossible {roots : List Nat} {T L : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (ess : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hnz : normPack (obs T) ≠ 0 := by rwa [hnormT]
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left hnz
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha'
    exact normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have heq : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    exact ⟨fun ha' => raw_required run roots a sub (ess a ha'), sub a⟩
  by_contra! small
  exact noRun k (by omega) (heq.symm ▸ run)
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def Slice (raw : List Nat) (T d : Nat) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Nat),
    (∀ r : Row, d.testBit (f r).val = true) ∧
    (∀ a ∈ raw, Avail (roots.map obs) (restrictW f (obs a))) ∧
    ¬Constant (restrictW f (obs T)) ∧
    ∀ p bank, Reach (roots.map obs) p bank → Avail bank (restrictW f (obs T)) → L ≤ p
def isConstM (d a : Nat) : Bool := (a &&& d == 0) || (a &&& d == d)
def availM (d : Nat) (pm : List Nat) (a : Nat) : Bool :=
  let m := a &&& d
  m == 0 || m == d || pm.contains m || pm.contains (d ^^^ m)
lemma masked_eq_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (b &&& d)) : restrictW f (obs a) = restrictW f (obs b) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_zero_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = 0) : restrictW f (obs a) = fun _ => false := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_one_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = d) : restrictW f (obs a) = fun _ => true := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_comp_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (d ^^^ (b &&& d))) : restrictW f (obs a) = invW (restrictW f (obs b)) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simp only [Nat.testBit_and, Nat.testBit_xor, dom r, Bool.and_true] at h
  simp only [restrictW, obs, invW, h]
  cases b.testBit (f r).val <;> rfl
def poolSupply (f : Row → Row) (bank : List Wire) (pool : List Nat) : Prop :=
  ∀ a ∈ pool, Avail bank (restrictW f (obs a))
lemma availM_sound {f : Row → Row} {d a : Nat} {bank : List Wire} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hs : poolSupply f bank pool)
    (ok : availM d (pool.map (· &&& d)) a = true) :
    Avail bank (restrictW f (obs a)) := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at ok
  rcases ok with ((h0 | h1) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero_obs dom h0⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one_obs dom h1⟩)
  · exact (masked_eq_obs dom he.symm) ▸ hs v hv
  · have hinv := avail_inv (hs v hv)
    have hcomp : restrictW f (obs a) = invW (restrictW f (obs v)) := by
      have hx : (a &&& d) = d ^^^ (v &&& d) := by
        have := congrArg (d ^^^ ·) he
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_self] using this.symm
      exact masked_comp_obs dom hx
    exact hcomp ▸ hinv
abbrev Choice := Nat × Nat × Nat
def choiceVal (c : Choice) : Nat := bin c.1 c.2.1 c.2.2
def choiceOK (d : Nat) (pm : List Nat) (c : Choice) : Bool :=
  decide (c.1 < 4) && availM d pm c.2.1 && availM d pm c.2.2
def makePool (d : Nat) (pool : List Nat) : List Choice → Option (List Nat)
  | [] => some pool
  | c :: cs => if choiceOK d (pool.map (· &&& d)) c then makePool d (choiceVal c :: pool) cs else none
lemma pay_choice {f : Row → Row} {d : Nat} {roots bank q} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d (pool.map (· &&& d)) c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  have ha := availM_sound dom hs valid.1.2
  have hb := availM_sound dom hs valid.2
  have hprep : ∃ op x y, comb4 c.1 (restrictW f (obs c.2.1)) (restrictW f (obs c.2.2)) = comb2 op x y ∧
      Avail bank x ∧ Avail bank y := by
    have hd := valid.1.1
    interval_cases c.1
    · exact ⟨false, _, _, rfl, ha, hb⟩
    · exact ⟨true, _, _, rfl, ha, hb⟩
    · exact ⟨false, _, _, rfl, ha, avail_inv hb⟩
    · exact ⟨false, _, _, rfl, avail_inv ha, hb⟩
  obtain ⟨op, x, y, eq, hx, hy⟩ := hprep
  refine ⟨comb2 op x y :: bank, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · have hcv : restrictW f (obs (choiceVal c)) = comb2 op x y := by
      rw [← eq]; funext r; simp only [choiceVal, restrictW, obs, testBit_bin, comb4, comb2, invW]
      rcases c.1 with _ | _ | _ | d' <;> rfl
    exact hcv ▸ Or.inl (by simp)
  · exact avail_cons _ (hs v hv)
lemma makePool_sound {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {res} (ok : makePool d pool cs = some res) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next res := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction
lemma count_constM {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (ws : List Nat) : ws.countP (isConstM d) ≤ wmass ((ws.map obs).map (restrictW f)) := by
  classical
  induction ws with
  | nil => simp [wmass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, wmass, List.sum_cons] at ih ⊢
    cases h : isConstM d a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih.trans (Nat.le_add_left _ _)
    · have hc : Constant (restrictW f (obs a)) := by
        simp only [isConstM, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h0 | h1
        · exact ⟨false, masked_zero_obs dom h0⟩
        · exact ⟨true, masked_one_obs dom h1⟩
      simp only [ite_true, wcost, hc]
      omega
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  c.pm = c.wires.map (· &&& c.dom) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map fun pool => ⟨d, lb, cs.length, pool, pool.map (· &&& d)⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨rfl, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let z := choiceVal op
  let extra := !(availM c.dom c.pm z)
  decide (k + c.paid + extra.toNat < c.lb + (z :: rest).countP (isConstM c.dom)) &&
    rest.all (availM c.dom c.pm) && (!extra || choiceOK c.dom c.pm op)
lemma scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  obtain ⟨hpm, f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  intro t ht run
  have finish (n : Nat) (out : List Wire) (hr : Reach (roots.map obs) n out)
      (hsup : poolSupply f out (choiceVal op :: rest))
      (hle : n = c.paid + (!(availM c.dom c.pm (choiceVal op))).toNat) : False := by
    have hcov : Supply out (((choiceVal op :: rest).map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact hsup a ha
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction nc (restrict_run f (live_to_run run (choiceVal op :: rest) nd rfl)) (roots.map obs) hr hcov
    have hlo := lo q next hq hav
    have hcm := count_constM dom (choiceVal op :: rest)
    have hineq := cut.1.1
    omega
  cases hav : availM c.dom c.pm (choiceVal op) with
  | true =>
    apply finish c.paid bank hp _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact availM_sound dom hs (hpm ▸ hav)
    · exact availM_sound dom hs (hpm ▸ cut.1.2 a ha)
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      exact hpm ▸ h2
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (hpm ▸ cut.1.2 a ha)
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (127 ^^^ z)) ||| o) % 128, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 128
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 128 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^128) (hb : b < 2^128) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 128 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^128) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^128 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^128 := hS a (by simp)
    have hblt : b < 2^128 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^128 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^128 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^128 := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact hzlt; exact hUlt x hx
    have nr := ih tail htail_lt
    simp only [Finset.image_insert, renameW_bin] at nr ⊢
    refine ⟨U.image (renameW f), renameW f a, renameW f b, d, hd, rfl,
      fun hz => ha (renameW_inj f onto halt (by decide) (hz.trans (renameW_zero f).symm)),
      fun hz => hb (renameW_inj f onto hblt (by decide) (hz.trans (renameW_zero f).symm)),
      fun heq => hab (renameW_inj f onto halt hblt heq), ?_, nr⟩
    intro hm
    rw [← renameW_bin] at hm
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt halt heq]; simp)
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt hblt heq]; simp)
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
    exact fresh (by rw [renameW_inj f onto hzlt (hUlt x hx) heq.symm]; simp [hx])
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^128) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0
def ALL128 : Nat := 0xffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 128, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL128 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 7) (hj : j < 7) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 7 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL128 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
  | true =>
    obtain ⟨heq, h10, h01⟩ := hr.1 hms
    rw [heq]
    by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
    · simp [hd, h10 hd, h01]
    · simp [hd, h01]
  | false =>
    rcases hr.2 hms with ⟨hd, h10, heq, h01⟩ | ⟨h10, h01, heq⟩
    · simp [hd, h10, heq, h01]
    · by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
      · simp [hd, h10 hd, h01, heq]
      · simp [hd, h01, heq]
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) : swapWord i j w < 2^128 := by
  have hi : i < 7 := by omega
  have h1 : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^128 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^128 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^128 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 7)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^128) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^128 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hr⟩, testBit_renameW _ _ (swapRow p.1 p.2 ⟨r, hr⟩), testBit_renameW _ _ ⟨r, hr⟩]
      rfl
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega)))]
lemma permRow_surj (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) :
    Function.Surjective (permRow swaps) := by
  induction swaps with
  | nil => intro r; exact ⟨r, rfl⟩
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro r
    obtain ⟨q, hq⟩ := ih hv.2 r
    refine ⟨swapRow p.1 p.2 q, ?_⟩
    change permRow ps (swapRow p.1 p.2 (swapRow p.1 p.2 q)) = r
    rw [swapRow_invol p.1 p.2 (by omega) hv.1.2, hq]
lemma permRow_rev_cancel (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) (r : Row) :
    permRow swaps.reverse (permRow swaps r) = r := by
  induction swaps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
        swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
      simp [permRow, List.reverse_cons, List.foldl_append]
    rw [h1, ih hv.2, swapRow_invol p.1 p.2 (by omega) hv.1.2]
lemma rotate_impossible {T n : Nat} {ws : List Nat} (hi : Impossible T n ws.toFinset)
    (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (hT : T < 2^128) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^128) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^128 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^128 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
  have run' := live_renameW run hr (permRow swaps.reverse) (permRow_surj swaps.reverse hvr)
  have hT' : renameW (permRow swaps.reverse) T = T := by
    conv_lhs => rw [← hfix]
    exact hinv_word T hT
  have hS' : (ws.map (permWord swaps)).toFinset.image (renameW (permRow swaps.reverse)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hinv_word x (hw x hx)]
    · intro ha
      exact ⟨permWord swaps a, ⟨a, ha, rfl⟩, hinv_word a (hw a ha)⟩
  rw [hT', hS'] at run'
  exact hi k hk run'
abbrev Decor := Nat × Nat × Nat
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1, bin d x.2.1 y.2.1, bin d x.2.2 y.2.2)
def dsep (x : Decor) : Nat := x.2.1 ^^^ x.2.2
def projBits (rows : List Nat) (w : Nat) : Nat :=
  rows.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0
lemma testBit_projBits (rows : List Nat) (w i : Nat) :
    (projBits rows w).testBit i = match rows[i]? with | none => false | some r => w.testBit r := by
  induction rows generalizing i with
  | nil => simp [projBits]
  | cons r rs ih =>
    simp only [projBits, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.not_le.mpr (by decide : 0 < 1)]
      cases w.testBit r <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      have h0 : (if w.testBit r then (1 : Nat) else 0).testBit (i + 1) = false := by
        cases w.testBit r
        · simp
        · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
      rw [h0, Bool.or_false]
      exact ih i
lemma projBits_bin (rows : List Nat) (d a b : Nat) :
    projBits rows (bin d a b) = bin d (projBits rows a) (projBits rows b) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_projBits, testBit_bin, testBit_projBits, testBit_projBits]
  cases rows[i]? with
  | none => rcases d with _ | _ | _ | d <;> rfl
  | some r => exact testBit_bin d a b r
def faithful (pos neg : List Nat) (x : Decor) : Prop :=
  x.2.1 = projBits pos x.1 ∧ x.2.2 = projBits neg x.1
lemma faithful_bin {pos neg x y} (d : Nat) (hx : faithful pos neg x) (hy : faithful pos neg y) :
    faithful pos neg (dbin d x y) :=
  ⟨by rw [dbin, hx.1, hy.1, projBits_bin], by rw [dbin, hx.2, hy.2, projBits_bin]⟩
def goodPairs (T : Nat) (pos neg : List Nat) : Prop :=
  pos.length = neg.length ∧ ∀ i < pos.length,
    T.testBit (pos.getD i 0) = true ∧ T.testBit (neg.getD i 0) = false
def fullMask (n : Nat) : Nat := (1 <<< n) - 1
abbrev Cov := Nat × Nat × Nat
def addCov (z : Nat) (c : Cov) : Cov :=
  (z ||| c.1, (z ^^^ (z &&& c.1)) ||| (c.2.1 ^^^ (c.2.1 &&& z)),
   (z &&& c.2.1) ||| (c.2.2 ^^^ (c.2.2 &&& z)))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (dsep a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := c.1 ^^^ (c.1 &&& (c.2.1 &&& a))
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
lemma cov_one (c : Cov) (a : Nat) : takeOne (addCov a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOne, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
lemma cov_two (c : Cov) (a b : Nat) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwo, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma addCov_swap (c : Cov) (a b : Nat) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [addCov, Nat.testBit_or]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
      simp only [addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma cov_perm {l r : List Decor} (h : l.Perm r) : coverage l = coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (dsep a)) ih
  | swap _ _ _ => exact addCov_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
def delOne (ws : List Decor) (a : Decor) (k : Bool) : List Decor := if k then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
def restCov (c : Cov) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOne c b) else if kb then takeOne c a else takeTwo c a b
lemma cov_delOne {ws : List Decor} (a : Decor) (ha : a ∈ ws) (k : Bool) :
    (coverage (delOne ws a k)).1 = if k then (coverage ws).1 else takeOne (coverage ws) (dsep a) := by
  cases k
  · change (coverage (ws.erase a)).1 = _
    rw [cov_perm (List.perm_cons_erase ha)]
    exact (cov_one _ _).symm
  · rfl
lemma cov_delTwo {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb := by
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
    have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hbm))
    change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm hp]
    exact (cov_two _ _ _).symm
  · exact cov_delOne a ha false
  · exact cov_delOne b hb false
  · rfl
lemma cov_testBit (ws : List Decor) (i : Nat) :
    (coverage ws).1.testBit i = true ↔ ∃ x ∈ ws, (dsep x).testBit i = true := by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change (dsep a ||| (coverage ws).1).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp
lemma cov_required {T k pos neg} {ws : List Decor}
    (gp : goodPairs T pos neg) (hf : ∀ x ∈ ws, faithful pos neg x)
    (h : Live T k (ws.map Prod.fst).toFinset) :
    ((coverage ws).1 &&& fullMask pos.length) = fullMask pos.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have hfm : (fullMask pos.length).testBit i = decide (i < pos.length) := by
    simp [fullMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · have ⟨hp, hn⟩ := gp.2 i hi
    have hsep : T.testBit (pos.getD i 0) ≠ T.testBit (neg.getD i 0) := by rw [hp, hn]; decide
    obtain ⟨v, hv, hvd⟩ := live_sep h hsep
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hfx := hf x hx
    have hpi : pos[i]? = some (pos.getD i 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hni : neg[i]? = some (neg.getD i 0) := by
      have hi' : i < neg.length := gp.1 ▸ hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    have hbit : (dsep x).testBit i = true := by
      simp only [dsep, Nat.testBit_xor, hfx.1, hfx.2, testBit_projBits, hpi, hni]
      have h12 : x.1.testBit (pos.getD i 0) ≠ x.1.testBit (neg.getD i 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        exact hvd
      cases h1 : x.1.testBit (pos.getD i 0) <;> cases h2 : x.1.testBit (neg.getD i 0)
      · exact absurd (h1.trans h2.symm) h12
      · rfl
      · rfl
      · exact absurd (h1.trans h2.symm) h12
    have hc := (cov_testBit ws i).mpr ⟨x, hx, hbit⟩
    simp [hfm, hi, hc]
  · simp [hfm, hi]
def insertNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs
def sortNats : List Nat → List Nat
  | [] => []
  | a :: bs => insertNat a (sortNats bs)
lemma insertNat_perm (a : Nat) (l : List Nat) : (insertNat a l).Perm (a :: l) := by
  induction l with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp [insertNat, h]
    · exact by simpa [insertNat, h] using (List.Perm.cons b ih).trans (.swap a b bs)
lemma sortNats_perm (l : List Nat) : (sortNats l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertNat_perm a (sortNats bs)).trans (.cons a ih)
lemma sortNats_toFinset (l : List Nat) : (sortNats l).toFinset = l.toFinset := by
  ext x; simpa only [List.mem_toFinset] using (sortNats_perm l).mem_iff
def childTwo (ws : List Nat) (a b d : Nat) (ka kb : Bool) : List Nat :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma erase_toFinset {l : List Nat} (nd : l.Nodup) (a : Nat) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [nd.mem_erase_iff]
lemma enum_step {T cap : Nat} {ws : List Nat} (nd : ws.Nodup) (out : T ∉ ws)
    (stepOK : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb : Bool,
      a ≠ b → bin d a b ≠ 0 → bin d a b ∉ ws → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  cases k with
  | zero =>
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  | succ k =>
    obtain ⟨U, a, b, d, hd, he, _, _, hab, hf, tail⟩ := h
    have am : a ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_self a _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    have fresh : bin d a b ∉ ws := fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hnz : bin d a b ≠ 0 := live_nonzero tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b from rfl, erase_toFinset (nd.erase _) b, erase_toFinset nd a]
    have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
      cases c <;> simp [kept]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kf, kf, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (nd.erase _).erase _
    have ar : a ∉ rest := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (nd.erase a).not_mem_erase
    have nk := kept_nodup kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have ndc : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr hm))),
        kept_nodup ka a _ nk ax⟩
    have eqc : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := live_size tail
    have hlen : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup ndc, eqc]; omega
    exact stepOK a am b bm d hd ka kb hab hnz fresh hlen k (by omega) (eqc.symm ▸ tail)
lemma delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k; exact List.erase_sublist; exact List.Sublist.refl _
lemma delTwo_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) : (delTwo ws a b ka kb).Sublist ws :=
  (delOne_sub _ _ _).trans (delOne_sub _ _ _)
lemma delTwo_len (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
  cases ka <;> cases kb <;> simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
lemma unique_fst {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hn (eq ▸ List.mem_map_of_mem hb')).elim
    · exact (hn (eq.symm ▸ List.mem_map_of_mem ha')).elim
    · exact ih ht ha' hb'
lemma delTwo_map_toFinset {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  have wn : ws.Nodup := nd.of_map
  have dn : (delOne ws a ka).Nodup := wn.sublist (delOne_sub ws a ka)
  have m1 (l : List Decor) (hl : l.Nodup) (x y : Decor) (c : Bool) :
      y ∈ delOne l x c ↔ y ∈ l ∧ (y ≠ x ∨ c = true) := by
    cases c <;> simp [delOne, hl.mem_erase_iff, and_comm]
  have km (v : Nat) : v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
    simp only [delTwo, List.mem_map, m1 _ wn, m1 _ dn]
    constructor
    · rintro ⟨w, ⟨⟨hw, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, h1.imp (fun h e => h (unique_fst nd hw ha e)) id,
        h2.imp (fun h e => h (unique_fst nd hw hb e)) id⟩
    · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hw, h1.imp (fun h e => h (congrArg Prod.fst e)) id⟩,
        h2.imp (fun h e => h (congrArg Prod.fst e)) id⟩, rfl⟩
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (v : Nat) : v ∈ kept c x l ↔ (v = x ∧ c = true) ∨ v ∈ l := by
    cases c <;> simp [kept]
  ext v
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, km, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all
lemma childTwo_swap (v : List Nat) (nd : v.Nodup) (a b : Nat) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (y : Nat) : y ∈ kept c x l ↔ (y = x ∧ c = true) ∨ y ∈ l := by
    cases c <;> simp [kept]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm_flip d hd a b]
  tauto
def varsOf (m : Nat) : List Nat :=
  (List.range 7).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    let fr := ((r &&& (127 ^^^ z)) ||| o) % 128
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 128
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 128 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127 : ((r.val &&& (127 ^^^ z)) ||| o) < 128 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (127 ^^^ z)) < 128 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 7) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (127 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 7
    · have h7 : (127 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 128) && decide (s < 128) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL128 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL128]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 128 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^128) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^128 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^128) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^128 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def carryOK (swaps : List (Nat × Nat)) (roots1 : List Nat) (T1 : Nat) (roots2 : List Nat) (T2 : Nat) : Bool :=
  swapsValid swaps && checkProper T1 && checkRoots roots1 && checkProper T2 &&
    (permWord swaps T1 == T2) && roots1.all (fun a => freeIn roots2 (permWord swaps a))
lemma carry_of {swaps roots1 T1 roots2 T2 L} (ok : carryOK swaps roots1 T1 roots2 T2 = true)
    (hL : Lower roots2 T2 L) : Lower roots1 T1 L := by
  simp only [carryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hsv, hT1⟩, hR1⟩, hT2⟩, heq⟩, hcov⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT1
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hT2
  have hR1' := checkRoots_sound hR1
  have heq' : renameW (permRow swaps) T1 = T2 := (permWord_eq_renameW swaps hsv T1 p1b).symm.trans heq
  have hcov' : ∀ a ∈ roots1, Avail (roots2.map obs) (restrictW (permRow swaps) (obs a)) := fun a ha =>
    freeIn_sound (permWord_eq_renameW swaps hsv a (hR1' a ha).1 ▸ hcov a ha)
  simpa using lower_slice p1a p1b p1c hR1' p2a p2b p2c (permRow swaps) heq' hcov' ∅ (by simp) (by simp) L hL
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL128))
lemma lift_of {z o roots T other G essPairs L} (ok : liftCheck z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G := (fixWord_eq_renameW z o T).symm.trans heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL128]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 128 r'.val |> fun e => by simpa [this] using e⟩
def goodPairsCheck (T : Nat) (pos neg : List Nat) : Bool :=
  (pos.length == neg.length) &&
    (List.range pos.length).all fun i => T.testBit (pos.getD i 0) && !(T.testBit (neg.getD i 0))
lemma goodPairs_of {T pos neg} (ok : goodPairsCheck T pos neg = true) : goodPairs T pos neg := by
  simp only [goodPairsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at ok
  exact ok
def autosCheck (T : Nat) (autos : List (List (Nat × Nat))) : Bool :=
  autos.all fun sw => swapsValid sw && (permWord sw T == T)
lemma autos_of {T autos} (ok : autosCheck T autos = true) :
    ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T := by
  simp only [autosCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok
def baseCheck (pos neg : List Nat) (base : List Decor) : Bool :=
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^128)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := by
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  intro x hx
  have h := ok x hx
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
def forestRootCheck (roots : List Nat) (T : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    roots.all fun a => essPairs.any fun e => (e.1 == a) && checkEss1 T roots e.1 e.2.1 e.2.2
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat

def nodesWithIdentity (entries : List (List Nat × List Nat)) : List NodeSpec :=
  entries.map (fun entry => (entry.1, entry.2, [0]))

lemma var_testBit (i : Fin 7) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
def sliceDirectCheck (z o zDead : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    decide (zDead < 128) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead : Nat) (hz : z < 128) (hd : zDead < 128) (ho : o < 128)
    (hzo : ((z ||| zDead) &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true := by
  have hsub := subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n := 7) hz hd) ho hzo r
  unfold subcube at hsub ⊢
  rw [testBit_foldr_bits] at hsub ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsub ⊢
  refine ⟨hsub.1, ?_, hsub.2.2⟩
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun x => x.testBit i) hsub.2.1
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  cases hfa : (fixRow (z ||| zDead) o r).val.testBit i <;> cases hzb : z.testBit i <;> simp_all
lemma slice_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) qL := by
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, ho⟩, _hzo0⟩, hd⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  refine ⟨fixRow (z ||| zDead) o, qRoots, subcube_fixRow_sup z o zDead hz hd ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW (z ||| zDead) o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW, heq]
  exact hPrior
def evalInput6 (r : Row) : Fin 6 → Bool := fun i => r.val.testBit i.val
def packInput6 (x : Fin 6 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    omega⟩
lemma evalInput6_packInput6 (x : Fin 6 → Bool) : evalInput6 (packInput6 x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (j : Fin 6),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
  fin_cases i <;> simpa [evalInput6, packInput6] using hi
lemma sum_eq_packInput6 (x : Fin 6 → Bool) :
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = (packInput6 x).val := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two, packInput6]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide
lemma testBit_rep64 (T6 : Nat) (hT6 : T6 < 2^64) (r : Row) :
    (T6 ||| (T6 <<< 64)).testBit r.val = T6.testBit (r.val % 64) := by
  have hr := r.isLt
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h64 : r.val < 64
  · have hn : ¬(64 ≤ r.val) := by omega
    rw [Nat.mod_eq_of_lt h64]
    simp [hn]
  · have hge : 64 ≤ r.val := by omega
    have hmod : r.val % 64 = r.val - 64 := by omega
    rw [hmod]
    have hhi : T6.testBit r.val = false → (T6.testBit r.val || (decide (64 ≤ r.val) && T6.testBit (r.val - 64))) = T6.testBit (r.val - 64) := by
      intro hf; simp [hf, hge]
    have hf : T6.testBit r.val = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hT6 (Nat.pow_le_pow_right (by decide : 0 < 2) hge))
    exact hhi hf
lemma sw_extract_full_6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^128 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput6 r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi6 : i < 6 := by simpa using hi2
      have hv : (varsOf 63)[i]? = some (VAR i) := by interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput6, swRead, Bool.false_bne]
      have hget : (varsOf 63)[i]'(by simpa [seeds] using hi1) = VAR i := (List.getElem?_eq_some_iff.mp hv).2
      rw [hget]
      exact var_testBit ⟨i, by omega⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · have h := hev ⟨r, hr⟩; simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]; exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma table2_of_lower (T6 : Nat) (hT6lt : T6 < 2^64)
    (hT0 : (T6 ||| (T6 <<< 64)) ≠ 0) (hTlt : (T6 ||| (T6 <<< 64)) < 2^128) (hTb0 : (T6 ||| (T6 <<< 64)).testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 63) (T6 ||| (T6 <<< 64)) L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = (T6 ||| (T6 <<< 64)).testBit r.val)
    (s : ℕ)
    (hcs : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  let T := T6 ||| (T6 <<< 64)
  obtain ⟨C, hfan, hsize, heval⟩ := hcs
  have hlegal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have ⟨hm, hl⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    exact ⟨hm, hl⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · have hlt : C.gates.countP isBin < C.gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    have heR : ∀ r : Row, Circuit.eval ⟨C.gates, C.output⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val := by
      intro r
      have h1 := heval (evalInput6 r)
      have hsum : (∑ i : Fin 6, if evalInput6 r i then 2 ^ (i : ℕ) else 0) = r.val % 64 := by
        rw [sum_eq_packInput6]
        have h : ∀ j : Row, (packInput6 (evalInput6 j)).val = j.val % 64 := by decide +kernel
        exact h r
      dsimp only at h1
      rw [hsum] at h1
      exact h1.trans (testBit_rep64 T6 hT6lt r).symm
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full_6 T hT0 hTlt hTb0 C.gates C.output hlegal heR
    have hrun := live_to_run hlive S.toList (Finset.nodup_toList S) (by simp)
    have hsup : Supply ((varsOf 63).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 63).map obs)
        (show Reach ((varsOf 63).map obs) 0 ((varsOf 63).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    have hwEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
      intro x
      rw [← evalInput6_packInput6 x, hwEvalR (packInput6 x), testBit_rep64 T6 hT6lt (packInput6 x)]
      rw [evalInput6_packInput6 x, sum_eq_packInput6 x]
      have hlt64 : (packInput6 x).val < 64 := by
        have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
        have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
        simp only [packInput6]; omega
      rw [Nat.mod_eq_of_lt hlt64]
    have hcsz : C.size = C.gates.length := rfl
    refine ⟨⟨wit, wo⟩, hwMono, ?_, hwEval⟩
    change wit.length ≤ s
    omega
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    have ⟨hm, hl⟩ := hlegal g hg
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
inductive BT (α : Type) where
  | empty : BT α
  | leaf : α → BT α
  | node : BT α → BT α → BT α
def btGet {α : Type} (d : α) : BT α → Nat → α
  | .empty, _ => d
  | .leaf x, _ => x
  | .node l r, i => if i &&& 1 == 0 then btGet d l (i >>> 1) else btGet d r (i >>> 1)
def btSet {α : Type} : Nat → BT α → Nat → α → BT α
  | 0, _, _, v => .leaf v
  | d + 1, .empty, i, v =>
    if i &&& 1 == 0 then .node (btSet d .empty (i >>> 1) v) .empty
    else .node .empty (btSet d .empty (i >>> 1) v)
  | d + 1, .leaf x, i, v =>
    if i &&& 1 == 0 then .node (btSet d (.leaf x) (i >>> 1) v) .empty
    else .node .empty (btSet d (.leaf x) (i >>> 1) v)
  | d + 1, .node l r, i, v =>
    if i &&& 1 == 0 then .node (btSet d l (i >>> 1) v) r
    else .node l (btSet d r (i >>> 1) v)
def btUpdate {α : Type} (d0 : α) : Nat → BT α → Nat → (α → α) → BT α
  | 0, .leaf x, _, f => .leaf (f x)
  | 0, _, _, f => .leaf (f d0)
  | d + 1, .empty, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d .empty (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d .empty (i >>> 1) f)
  | d + 1, .leaf x, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d (.leaf x) (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d (.leaf x) (i >>> 1) f)
  | d + 1, .node l r, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d l (i >>> 1) f) r
    else .node l (btUpdate d0 d r (i >>> 1) f)
def btAll {α : Type} (P : α → Prop) : BT α → Prop
  | .empty => True
  | .leaf x => P x
  | .node l r => btAll P l ∧ btAll P r
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction t generalizing i with
  | empty => exact hd
  | leaf x => exact ht
  | node l r ihl ihr =>
    unfold btGet
    split
    · exact ihl ht.1 _
    · exact ihr ht.2 _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact hv
  | succ d ih =>
    cases t with
    | empty =>
      unfold btSet; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btSet; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btSet; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases t with
    | leaf x => exact hf x ht
    | empty => exact hf d0 hd0
    | node _ _ => exact hf d0 hd0
  | succ d ih =>
    cases t with
    | empty =>
      unfold btUpdate; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btUpdate; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btUpdate; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
def btOfList {α : Type} (depth : Nat) (l : List α) : BT α :=
  (l.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) (0, BT.empty)).2
lemma btAll_ofList {α : Type} {P : α → Prop} {depth : Nat} {l : List α}
    (h : ∀ x ∈ l, P x) : btAll P (btOfList depth l) := by
  unfold btOfList
  have hgo : ∀ (xs : List α) (acc : Nat × BT α),
      (∀ x ∈ xs, P x) → btAll P acc.2 →
      btAll P (xs.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) acc).2 := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; exact hacc
    | cons x xs ih =>
      intro acc hx hacc
      exact ih (acc.1 + 1, btSet depth acc.2 acc.1 x)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (btAll_set hacc (hx x (List.mem_cons_self ..)))
  exact hgo l (0, BT.empty) h trivial
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL128 ^^^ VAR i else if o.testBit i then VAR i else ALL128
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 7) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL128.testBit r.val = true := by
    simp only [ALL128]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 128 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · have hsub : (subcube z o).testBit r = ((r &&& z == 0) && (r &&& o == o)) := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and,
      fastBitMask_testBit z o 0 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 1 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 2 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 3 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 4 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 7) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 7, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 7
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 7
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 128 ≤ r := by omega
      have ha : ALL128 < 2^128 := by decide
      have hv : VAR i < 2^128 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^128; decide
      have hlt_m : fastBitMask z o i < 2^128 := by
        unfold fastBitMask; split
        · exact Nat.xor_lt_two_pow ha hv
        · split; exact hv; exact ha
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by decide : 0 < 2) hle))
    have hsub : (subcube z o).testBit r = false := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and, hlt_f]
    rfl
lemma slice_fast_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  have ok2 := ok
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1.1.1 ok2.1.1.1.1.1.1.1.2 ok2.1.1.1.1.1.1.2]
  exact slice_direct ok hPrior
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) &&& 63
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (ws.map (permWord sw)))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContainsBT at hhit
    have hmem := List.contains_iff_mem.mp hhit
    have hb : ∀ xs ∈ btGet [] prevBks (hashWs64 (sortNats ((choiceVal op :: rest).map (permWord sw)))),
        Impossible T k xs.toFinset :=
      btAll_get hPrev (fun _ hx => (List.not_mem_nil hx).elim) _
    have himp := hb _ hmem
    rw [sortNats_toFinset] at himp
    have ⟨hsv, hfix⟩ := hAutos sw hsw
    have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
    have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
        ∀ r : Row, permRow l.reverse (permRow l r) = r := by
      intro l hl
      induction l with
      | nil => intro r; rfl
      | cons p ps ih =>
        simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
        intro r
        have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
            swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
          simp [permRow, List.reverse_cons, List.foldl_append]
        rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
    have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
      simpa using hinv_row_gen sw.reverse hvr
    have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 128
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rw [permWord_eq_renameW sw hsv x (hlt x hx)]
      exact renameW_lt _ x
    have hrot := rotate_impossible himp sw.reverse hvr hT hfixr hmap_lt
    have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
      exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
    rwa [hback] at hrot
abbrev FastPool := BoundPool × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else some (c, miss, vals.countP (isConstM c.dom))
def fastPoolCut (fp : FastPool) (k : Nat) (a b d : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let totC := fp.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && isConstM c.dom a then 1 else 0
    let dropB := if !kb && isConstM c.dom b then 1 else 0
    let z := bin d a b
    let cRest := totC - dropA - dropB + (if isConstM c.dom z then 1 else 0)
    let zIn := availM c.dom c.pm z
    let extra := if zIn then 0 else 1
    decide (k + c.paid + extra < c.lb + cRest) && (zIn || choiceOK c.dom c.pm (d, a, b))
lemma countP_erase {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {x : α} (hx : x ∈ l) :
    (l.erase x).countP p + (if p x then 1 else 0) = l.countP p := by
  have hp := List.perm_cons_erase hx
  have h1 := List.Perm.countP_eq p hp
  simp only [List.countP_cons] at h1
  omega
lemma countP_delTwo_fst (p : Nat → Bool) {ws : List Decor} {a b : Decor}
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map Prod.fst).countP p =
      (ws.map Prod.fst).countP p - (if !ka && p a.1 then 1 else 0) - (if !kb && p b.1 then 1 else 0) := by
  have hne : a ≠ b := fun e => hab (congrArg Prod.fst e)
  have hmap_erase : ∀ (l : List Decor) (x : Decor), (l.map Prod.fst).Nodup → x ∈ l →
      (l.erase x).map Prod.fst = (l.map Prod.fst).erase x.1 := by
    intro l x hnd hx
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne1 : y.1 ≠ x.1 := by
          intro eq; apply hnd.1; rw [eq]
          exact List.mem_map_of_mem ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))
        have h1 : (y == x) = false := beq_false_of_ne hyx
        have h2 : (y.1 == x.1) = false := beq_false_of_ne hne1
        simp only [List.erase_cons, h1, h2, List.map_cons]
        exact congrArg (y.1 :: ·) (ih hnd.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx)))
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne hne.symm).mpr hb
    have hnd1 : ((ws.erase a).map Prod.fst).Nodup := ((List.erase_sublist).map Prod.fst).nodup nd
    change (((ws.erase a).erase b).map Prod.fst).countP p = _
    rw [hmap_erase _ b hnd1 hbm, hmap_erase ws a nd ha]
    have ha1 : a.1 ∈ ws.map Prod.fst := List.mem_map_of_mem ha
    have hb1 : b.1 ∈ (ws.map Prod.fst).erase a.1 := (List.mem_erase_of_ne hab.symm).mpr (List.mem_map_of_mem hb)
    have c1 := countP_erase p ha1
    have c2 := countP_erase p hb1
    cases hpa : p a.1 <;> cases hpb : p b.1 <;> simp [hpa, hpb] at c1 c2 ⊢ <;> omega
  · change ((ws.erase a).map Prod.fst).countP p = _
    rw [hmap_erase ws a nd ha]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) ha)
    cases hpa : p a.1 <;> simp [hpa] at c1 ⊢ <;> omega
  · change ((ws.erase b).map Prod.fst).countP p = _
    rw [hmap_erase ws b nd hb]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) hb)
    cases hpb : p b.1 <;> simp [hpb] at c1 ⊢ <;> omega
  · simp [delTwo, delOne]
lemma fastPoolCut_sound {raw T ws a b d ka kb k c fp}
    (hP : ValidPool raw T c) (hprep : prepPool (ws.map Prod.fst) c = some fp)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 d ka kb = true) :
    Impossible T k (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  unfold prepPool at hprep
  dsimp only at hprep
  split at hprep
  · simp at hprep
  · simp only [Option.some.injEq] at hprep
    subst hprep
    unfold fastPoolCut at hcut
    dsimp only at hcut
    split at hcut
    · simp at hcut
    · next hmiss =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_filter, Bool.not_eq_true'] at hmiss
      have hsub := (delTwo_sub ws a b ka kb).map Prod.fst
      have h_all_avail : ((delTwo ws a b ka kb).map Prod.fst).all (availM c.dom c.pm) = true := by
        rw [List.all_eq_true]; intro w hw
        by_contra hna
        have hnf : availM c.dom c.pm w = false := Bool.eq_false_iff.mpr hna
        have hmem_ws : w ∈ ws.map Prod.fst := hsub.subset hw
        have hm := hmiss w ⟨hmem_ws, hnf⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
        have hne_ab : a ≠ b := fun e => hab (congrArg Prod.fst e)
        have hnot_in : ∀ (x : Decor) (kx : Bool), kx = false → x ∈ ws → x.1 ∉ (delTwo ws a b ka kb).map Prod.fst → True := fun _ _ _ _ _ => trivial
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            exact List.Nodup.not_mem_erase hnd_ws hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · have hu_eq : u = a := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa)
          exact hna' hka hu_eq
        · have hu_eq : u = b := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb)
          exact hnb' hkb hu_eq
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut
      simp only [choiceVal, h_all_avail, Bool.true_and, Bool.and_true, List.countP_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hcut ⊢
      rw [hcnt]
      rcases hcut with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          cases hcz : isConstM c.dom (bin d a.1 b.1) <;>
          simp only [hz, hcz, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
            Bool.and_eq_true, Bool.false_eq_true, ite_true, ite_false] at h1 ⊢ <;> omega
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          simp only [hz, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or] at h2 ⊢ <;>
          exact h2
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
  go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^128) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hfr_b : (ws.any (fun v => v.1 == z.1)) = false := by
    rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
    have hvz : v.1 = bin d a.1 b.1 := beq_iff_eq.mp heq
    exact hfr (hvz ▸ List.mem_map_of_mem hv)
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    have hdl := delTwo_len ws a b ka kb ha hb ne
    simp only [child, rest, List.length_map, List.length_cons]
    omega
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMoveBT at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAllBT, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma nodeBT_sound {raw T pos neg ws fpools autos prevBks cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (checks : cap = 0 ∨ testAllBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0
    intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPairBT, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMoveBT_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAllBT_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
def buildWiresBT (depth : Nat) (base : List Decor) (steps : List (Nat × Nat × Nat)) : BT Decor :=
  let init := (base.length, btOfList depth base)
  (steps.foldl (fun p s =>
    let a := btGet (0, 0, 0) p.2 s.2.1
    let b := btGet (0, 0, 0) p.2 s.2.2
    (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 a b))) init).2
lemma buildWiresBT_faithful {depth pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128)
        (ss.foldl (fun p s => (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 (btGet (0, 0, 0) p.2 s.2.1) (btGet (0, 0, 0) p.2 s.2.2)))) acc).2 := by
    intro ss
    induction ss with
    | nil => intro acc hacc; exact hacc
    | cons s ss ih =>
      intro acc hacc
      have ha := btAll_get hacc hdef s.2.1
      have hb := btAll_get hacc hdef s.2.2
      exact ih _ (btAll_set hacc ⟨faithful_bin s.1 ha.1 hb.1, bin_lt s.1 _ _ ha.2 hb.2⟩)
  exact hgo steps (base.length, btOfList depth base) h0
def buildPoolsBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : List PoolSpec) : BT (Option BoundPool) :=
  btOfList pdepth (pspecs.map fun (slIdx, chIdxs) =>
    match btGet none slices slIdx with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
      materialize raw cs dom lb)
lemma buildPoolsBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))} {pspecs : List PoolSpec}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsBT pdepth W raw slices pspecs) := by
  apply btAll_ofList
  intro o ho c hc
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp ho
  dsimp only at hmat
  have hsl := btAll_get (d := none) hSlices (fun _ h => by simp at h) slIdx
  cases heq : btGet none slices slIdx with
  | none => rw [heq] at hmat; exact absurd (hmat.trans hc) (by simp)
  | some sl =>
    rw [heq] at hmat
    exact materialize_sound (hsl sl heq) (hmat.trans hc)
def checkNodeBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals := ws.map Prod.fst
  let fpools := ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos := ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^128 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun fp hfp => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hfp
      cases heq : btGet none poolTable pIdx with
      | none => simp [heq] at hmat
      | some c =>
        simp only [heq] at hmat
        have hvc := btAll_get hPoolTable (fun _ h => by simp at h) pIdx c heq
        have hfp_eq : fp.1 = c := by
          unfold prepPool at hmat
          dsimp only at hmat
          split at hmat
          · simp at hmat
          · simp only [Option.some.injEq] at hmat; rw [← hmat]
        rw [hfp_eq]
        exact ⟨hvc, hmat⟩)
    (fun sw hsw => by
      obtain ⟨aIdx, _, rfl⟩ := List.mem_map.mp hsw
      exact btAll_get hAutos ⟨rfl, rfl⟩ aIdx)
    hPrev ok.2
def nodeValsBT (W : BT Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (btGet (0, 0, 0) W idx).1)
def buildBucketsBT (W : BT Decor) (nodes : List NodeSpec) : BT (List (List Nat)) :=
  nodes.foldl (fun acc ns =>
    let xs := nodeValsBT W ns
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := fun ns hns => by
    unfold nodeValsBT; rw [sortNats_toFinset]
    exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
lemma lower_of_forestBT {roots T cap} {topBks : BT (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : btAll (fun bk => ∀ xs ∈ bk, Impossible T cap xs.toFinset) topBks)
    (hRoot : bucketContainsBT topBks roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContainsBT at hRoot
    exact btAll_get hTop (fun _ h => (List.not_mem_nil h).elim) _ _ (List.contains_iff_mem.mp hRoot)
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
namespace Cofactor12080
def G_0 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def R_0 : List Nat := varsOf 52
def pos_0 : List Nat := [20,20,36,36,48,48,20,36,48]
def neg_0 : List Nat := [16,4,32,4,32,16,32,16,4]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 2,20,16),(VAR 4,20,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_5 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def R_5 : List Nat := varsOf 13
lemma low_5_ok : carryOK [(3,5),(1,4),(0,1),(0,2)] R_5 G_5 R_0 G_0 = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 4 := carry_of low_5_ok low_0

def G_7 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def R_7 : List Nat := varsOf 37
lemma low_7_ok : carryOK [(1,3),(1,4),(0,1),(0,2)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0

def G_8 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def R_8 : List Nat := varsOf 14
lemma low_8_ok : carryOK [(3,5),(1,4),(1,2)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0

def G_9 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_9 : List Nat := varsOf 22
lemma low_9_ok : carryOK [(3,5),(1,3),(1,4),(1,2)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0

def G_10 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_10 : List Nat := varsOf 38
lemma low_10_ok : carryOK [(1,3),(1,4),(1,2)] R_10 G_10 R_0 G_0 = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 4 := carry_of low_10_ok low_0

def G_17 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def R_17 : List Nat := varsOf 50
lemma low_17_ok : carryOK [(1,2)] R_17 G_17 R_0 G_0 = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 4 := carry_of low_17_ok low_0

def G_18 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def R_18 : List Nat := varsOf 54
def pos_18 : List Nat := [22,22,22,38,38,38,50,50,50,52,52,52,22,22,22,38,38,38,50,50,50,52,52,52]
def neg_18 : List Nat := [20,18,6,36,34,6,48,34,18,48,36,20,34,36,48,18,20,48,6,20,36,6,18,34]
def fmask_18 : Nat := fullMask 24
def base_18 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xffff0000ffff0000ffff0000ffff0000,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_18 : List (Nat × Nat × Nat) := [(0,0,1),(3,4,2),(0,0,2),(0,4,2),(0,1,2),(3,7,3)]
def W_18 : BT Decor := buildWiresBT 4 base_18 steps_18
def autosL_18 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_18 : BT (List (Nat × Nat)) := btOfList 4 autosL_18
def slicesL_18 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def slices_18 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_18
def ps_18 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_18 : BT (Option BoundPool) := buildPoolsBT 2 W_18 R_18 slices_18 ps_18
lemma gp_18 : goodPairs G_18 pos_18 neg_18 := goodPairs_of (by decide +kernel)
lemma base_18_ok : ∀ x ∈ base_18, faithful pos_18 neg_18 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_18_ok : btAll (fun x => faithful pos_18 neg_18 x ∧ x.1 < 2^128) W_18 := buildWiresBT_faithful base_18_ok
set_option maxRecDepth 500000 in
lemma autos_18_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_18 = G_18) autos_18 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_18_0_ok : sliceDirectCheck 0 16 0 R_18 G_18 R_10 G_10 = true := by decide +kernel
lemma sl_18_0 : Slice R_18 G_18 (subcubeFast 0 16) 4 := slice_fast_direct sl_18_0_ok low_10
lemma sl_18_1_ok : sliceDirectCheck 0 2 0 R_18 G_18 R_0 G_0 = true := by decide +kernel
lemma sl_18_1 : Slice R_18 G_18 (subcubeFast 0 2) 4 := slice_fast_direct sl_18_1_ok low_0
lemma sl_18_2_ok : sliceDirectCheck 0 4 0 R_18 G_18 R_17 G_17 = true := by decide +kernel
lemma sl_18_2 : Slice R_18 G_18 (subcubeFast 0 4) 4 := slice_fast_direct sl_18_2_ok low_17
lemma sl_18_3_ok : sliceDirectCheck 0 32 0 R_18 G_18 R_9 G_9 = true := by decide +kernel
lemma sl_18_3 : Slice R_18 G_18 (subcubeFast 0 32) 4 := slice_fast_direct sl_18_3_ok low_9
set_option maxRecDepth 500000 in
lemma slices_18_ok : btAll (fun o => ∀ p, o = some p → Slice R_18 G_18 p.1 p.2) slices_18 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_18 G_18 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_18_0) (forall_cons (fun _ h => by cases h; exact sl_18_1) (forall_cons (fun _ h => by cases h; exact sl_18_2) (forall_cons (fun _ h => by cases h; exact sl_18_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_18_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_18 G_18 c) P_18 := buildPoolsBT_sound slices_18_ok
def bk_18_init : BT (List (List Nat)) := BT.empty
lemma bk_18_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 (0 - 1) xs.toFinset) bk_18_init := trivial
def nodes_18_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_0 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_init 0 nodes_18_0 = true := by decide +kernel
def bk_18_0 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_0
set_option maxRecDepth 500000 in
lemma bk_18_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 0 xs.toFinset) bk_18_0 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_init_ok chk_18_0
def nodes_18_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_1 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_0 1 nodes_18_1 = true := by decide +kernel
def bk_18_1 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_1
set_option maxRecDepth 500000 in
lemma bk_18_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 1 xs.toFinset) bk_18_1 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_0_ok chk_18_1
def nodes_18_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_2 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_1 2 nodes_18_2 = true := by decide +kernel
def bk_18_2 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_2
set_option maxRecDepth 500000 in
lemma bk_18_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 2 xs.toFinset) bk_18_2 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_1_ok chk_18_2
def nodes_18_3 : List NodeSpec := [([4,6,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_3 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_2 3 nodes_18_3 = true := by decide +kernel
def bk_18_3 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_3
set_option maxRecDepth 500000 in
lemma bk_18_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 3 xs.toFinset) bk_18_3 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_2_ok chk_18_3
def nodes_18_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([4,6,1,2,3],[0,2],[0]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_4 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_3 4 nodes_18_4 = true := by decide +kernel
def bk_18_4 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_4
set_option maxRecDepth 500000 in
lemma bk_18_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 4 xs.toFinset) bk_18_4 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_3_ok chk_18_4
def nodes_18_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_5 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_4 5 nodes_18_5 = true := by decide +kernel
def bk_18_5 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_5
set_option maxRecDepth 500000 in
lemma bk_18_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 5 xs.toFinset) bk_18_5 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_4_ok chk_18_5
def nodes_18_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_18_6 : checkNodesBT W_18 G_18 fmask_18 P_18 autos_18 bk_18_5 6 nodes_18_6 = true := by decide +kernel
def bk_18_6 : BT (List (List Nat)) := buildBucketsBT W_18 nodes_18_6
set_option maxRecDepth 500000 in
lemma bk_18_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_18 6 xs.toFinset) bk_18_6 :=
  buildBucketsBT_sound (by decide) gp_18 W_18_ok P_18_ok autos_18_ok bk_18_5_ok chk_18_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_ok : forestRootCheck R_18 G_18 [(VAR 1,22,20),(VAR 2,22,18),(VAR 4,22,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_18_in : bucketContainsBT bk_18_6 R_18 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_18 : Lower R_18 G_18 7 := lower_of_forestBT root_18_ok bk_18_6_ok root_18_in

def G_19 : Nat := 0xfe80fe80fe80fe80fe80fe80fe80fe80
def R_19 : List Nat := varsOf 15
def pos_19 : List Nat := [7,7,7,9,9,10,10,11,12,12,13,14,7,9,9,9,10,10,10,12,12,12]
def neg_19 : List Nat := [6,5,3,8,1,8,2,3,8,4,5,6,8,3,5,6,3,5,6,3,5,6]
def fmask_19 : Nat := fullMask 22
def base_19 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf49f,0x1b6496),(0xcccccccccccccccccccccccccccccccc,0x718e7,0x2da8c5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x381f07,0x36ce03),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3feff8,0x1128)]
def steps_19 : List (Nat × Nat × Nat) := [(3,0,3),(1,0,3),(2,0,3),(0,0,3),(2,0,1),(1,0,1),(0,0,1),(3,1,5),(3,7,1),(0,1,5),(3,0,1),(3,8,2),(1,7,1),(1,8,2),(3,10,9)]
def W_19 : BT Decor := buildWiresBT 5 base_19 steps_19
def autosL_19 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_19 : BT (List (Nat × Nat)) := btOfList 3 autosL_19
def slicesL_19 : List (Option (Nat × Nat)) := []
def slices_19 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_19
def ps_19 : List PoolSpec := []
def P_19 : BT (Option BoundPool) := buildPoolsBT 1 W_19 R_19 slices_19 ps_19
lemma gp_19 : goodPairs G_19 pos_19 neg_19 := goodPairs_of (by decide +kernel)
lemma base_19_ok : ∀ x ∈ base_19, faithful pos_19 neg_19 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_19_ok : btAll (fun x => faithful pos_19 neg_19 x ∧ x.1 < 2^128) W_19 := buildWiresBT_faithful base_19_ok
set_option maxRecDepth 500000 in
lemma autos_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_19 = G_19) autos_19 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_19_ok : btAll (fun o => ∀ p, o = some p → Slice R_19 G_19 p.1 p.2) slices_19 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_19 G_19 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_19_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_19 G_19 c) P_19 := buildPoolsBT_sound slices_19_ok
def bk_19_init : BT (List (List Nat)) := BT.empty
lemma bk_19_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 (0 - 1) xs.toFinset) bk_19_init := trivial
def nodes_19_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_0 : checkNodesBT W_19 G_19 fmask_19 P_19 autos_19 bk_19_init 0 nodes_19_0 = true := by decide +kernel
def bk_19_0 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_0
set_option maxRecDepth 500000 in
lemma bk_19_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 0 xs.toFinset) bk_19_0 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok P_19_ok autos_19_ok bk_19_init_ok chk_19_0
def nodes_19_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_1 : checkNodesBT W_19 G_19 fmask_19 P_19 autos_19 bk_19_0 1 nodes_19_1 = true := by decide +kernel
def bk_19_1 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_1
set_option maxRecDepth 500000 in
lemma bk_19_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 1 xs.toFinset) bk_19_1 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok P_19_ok autos_19_ok bk_19_0_ok chk_19_1
def nodes_19_2 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_2 : checkNodesBT W_19 G_19 fmask_19 P_19 autos_19 bk_19_1 2 nodes_19_2 = true := by decide +kernel
def bk_19_2 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_2
set_option maxRecDepth 500000 in
lemma bk_19_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 2 xs.toFinset) bk_19_2 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok P_19_ok autos_19_ok bk_19_1_ok chk_19_2
def nodes_19_3 : List NodeSpec := [([6,4,1,2],[],[]),([11,0,2,3],[],[]),([12,0,2,3],[],[]),([0,13,2,3],[],[]),([8,14,2,3],[],[0]),([0,1,15,3],[],[]),([0,16,2,3],[],[]),([0,1,17,3],[],[]),([10,9,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_3 : checkNodesBT W_19 G_19 fmask_19 P_19 autos_19 bk_19_2 3 nodes_19_3 = true := by decide +kernel
def bk_19_3 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_3
set_option maxRecDepth 500000 in
lemma bk_19_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 3 xs.toFinset) bk_19_3 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok P_19_ok autos_19_ok bk_19_2_ok chk_19_3
def nodes_19_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([0,1,2,3,5],[],[0,1]),([6,0,1,2,3],[],[0]),([7,0,1,2,3],[],[0,1]),([8,0,1,2,3],[],[0]),([0,1,9,2,3],[],[0]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_4 : checkNodesBT W_19 G_19 fmask_19 P_19 autos_19 bk_19_3 4 nodes_19_4 = true := by decide +kernel
def bk_19_4 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_4
set_option maxRecDepth 500000 in
lemma bk_19_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 4 xs.toFinset) bk_19_4 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok P_19_ok autos_19_ok bk_19_3_ok chk_19_4
def nodes_19_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_19_5 : checkNodesBT W_19 G_19 fmask_19 P_19 autos_19 bk_19_4 5 nodes_19_5 = true := by decide +kernel
def bk_19_5 : BT (List (List Nat)) := buildBucketsBT W_19 nodes_19_5
set_option maxRecDepth 500000 in
lemma bk_19_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_19 5 xs.toFinset) bk_19_5 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok P_19_ok autos_19_ok bk_19_4_ok chk_19_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck R_19 G_19 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 3,9,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT bk_19_5 R_19 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_19 : Lower R_19 G_19 6 := lower_of_forestBT root_19_ok bk_19_5_ok root_19_in

def G_20 : Nat := 0xff00f000f0000000ff00f000f0000000
def R_20 : List Nat := varsOf 60
lemma low_20_ok : liftCheck 0 8 R_20 G_20 R_0 G_0 [(VAR 3,28,20)] = true := by decide +kernel
lemma low_20 : Lower R_20 G_20 5 := lift_of low_20_ok low_0

def G_21 : Nat := 0xffc0ffc0fcc0fcc0ffc0ffc0fcc0fcc0
def R_21 : List Nat := varsOf 46
lemma low_21_ok : liftCheck 32 0 R_21 G_21 R_8 G_8 [(VAR 5,40,8)] = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 5 := lift_of low_21_ok low_8

def G_23 : Nat := 0xfffffcfcfcfcc0c0fffffcfcfcfcc0c0
def R_23 : List Nat := varsOf 54
def pos_23 : List Nat := [6,6,18,18,20,20,34,34,36,36,48,48,6,6,18,18,20,20,34,34,36,36,48,48]
def neg_23 : List Nat := [4,2,16,2,16,4,32,2,32,4,32,16,16,32,4,32,2,32,4,16,2,16,2,4]
def fmask_23 : Nat := fullMask 24
def base_23 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf0cf,0x51008a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x333333,0x844221),(0xffff0000ffff0000ffff0000ffff0000,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def steps_23 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_23 : BT Decor := buildWiresBT 4 base_23 steps_23
def autosL_23 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_23 : BT (List (Nat × Nat)) := btOfList 4 autosL_23
def slicesL_23 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,4),some (subcubeFast 2 0,4),some (subcubeFast 32 0,4),some (subcubeFast 16 0,4)]
def slices_23 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_23
def ps_23 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_23 : BT (Option BoundPool) := buildPoolsBT 2 W_23 R_23 slices_23 ps_23
lemma gp_23 : goodPairs G_23 pos_23 neg_23 := goodPairs_of (by decide +kernel)
lemma base_23_ok : ∀ x ∈ base_23, faithful pos_23 neg_23 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_23_ok : btAll (fun x => faithful pos_23 neg_23 x ∧ x.1 < 2^128) W_23 := buildWiresBT_faithful base_23_ok
set_option maxRecDepth 500000 in
lemma autos_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_23 = G_23) autos_23 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_23_0_ok : sliceDirectCheck 4 0 0 R_23 G_23 R_17 G_17 = true := by decide +kernel
lemma sl_23_0 : Slice R_23 G_23 (subcubeFast 4 0) 4 := slice_fast_direct sl_23_0_ok low_17
lemma sl_23_1_ok : sliceDirectCheck 2 0 0 R_23 G_23 R_0 G_0 = true := by decide +kernel
lemma sl_23_1 : Slice R_23 G_23 (subcubeFast 2 0) 4 := slice_fast_direct sl_23_1_ok low_0
lemma sl_23_2_ok : sliceDirectCheck 32 0 0 R_23 G_23 R_9 G_9 = true := by decide +kernel
lemma sl_23_2 : Slice R_23 G_23 (subcubeFast 32 0) 4 := slice_fast_direct sl_23_2_ok low_9
lemma sl_23_3_ok : sliceDirectCheck 16 0 0 R_23 G_23 R_10 G_10 = true := by decide +kernel
lemma sl_23_3 : Slice R_23 G_23 (subcubeFast 16 0) 4 := slice_fast_direct sl_23_3_ok low_10
set_option maxRecDepth 500000 in
lemma slices_23_ok : btAll (fun o => ∀ p, o = some p → Slice R_23 G_23 p.1 p.2) slices_23 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_23 G_23 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_23_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_23 G_23 c) P_23 := buildPoolsBT_sound slices_23_ok
def bk_23_init : BT (List (List Nat)) := BT.empty
lemma bk_23_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 (0 - 1) xs.toFinset) bk_23_init := trivial
def nodes_23_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_0 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_init 0 nodes_23_0 = true := by decide +kernel
def bk_23_0 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_0
set_option maxRecDepth 500000 in
lemma bk_23_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 0 xs.toFinset) bk_23_0 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_init_ok chk_23_0
def nodes_23_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_1 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_0 1 nodes_23_1 = true := by decide +kernel
def bk_23_1 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_1
set_option maxRecDepth 500000 in
lemma bk_23_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 1 xs.toFinset) bk_23_1 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_0_ok chk_23_1
def nodes_23_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_2 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_1 2 nodes_23_2 = true := by decide +kernel
def bk_23_2 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_2
set_option maxRecDepth 500000 in
lemma bk_23_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 2 xs.toFinset) bk_23_2 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_1_ok chk_23_2
def nodes_23_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_3 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_2 3 nodes_23_3 = true := by decide +kernel
def bk_23_3 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_3
set_option maxRecDepth 500000 in
lemma bk_23_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 3 xs.toFinset) bk_23_3 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_2_ok chk_23_3
def nodes_23_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_4 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_3 4 nodes_23_4 = true := by decide +kernel
def bk_23_4 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_4
set_option maxRecDepth 500000 in
lemma bk_23_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 4 xs.toFinset) bk_23_4 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_3_ok chk_23_4
def nodes_23_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_5 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_4 5 nodes_23_5 = true := by decide +kernel
def bk_23_5 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_5
set_option maxRecDepth 500000 in
lemma bk_23_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 5 xs.toFinset) bk_23_5 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_4_ok chk_23_5
def nodes_23_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_23_6 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_5 6 nodes_23_6 = true := by decide +kernel
def bk_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_6
set_option maxRecDepth 500000 in
lemma bk_23_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 6 xs.toFinset) bk_23_6 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_5_ok chk_23_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck R_23 G_23 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT bk_23_6 R_23 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_23 : Lower R_23 G_23 7 := lower_of_forestBT root_23_ok bk_23_6_ok root_23_in

def G_24 : Nat := 0xe880e880e880e880e880e880e880e880
def R_24 : List Nat := varsOf 15
lemma low_24_ok : carryOK [(3,5),(0,4),(0,2),(0,1)] R_24 G_24 R_18 G_18 = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 7 := carry_of low_24_ok low_18

def G_28 : Nat := 0xee00ee0088008800ee00ee0088008800
def R_28 : List Nat := varsOf 43
lemma low_28_ok : carryOK [(1,4),(0,2)] R_28 G_28 R_20 G_20 = true := by decide +kernel
lemma low_28 : Lower R_28 G_28 5 := carry_of low_28_ok low_20

def G_33 : Nat := 0xfa00fa00a000a000fa00fa00a000a000
def R_33 : List Nat := varsOf 45
lemma low_33_ok : carryOK [(1,4),(0,1),(0,2)] R_33 G_33 R_20 G_20 = true := by decide +kernel
lemma low_33 : Lower R_33 G_33 5 := carry_of low_33_ok low_20

def G_38 : Nat := 0xfc00fc00c000c000fc00fc00c000c000
def R_38 : List Nat := varsOf 46
lemma low_38_ok : carryOK [(1,4),(1,2)] R_38 G_38 R_20 G_20 = true := by decide +kernel
lemma low_38 : Lower R_38 G_38 5 := carry_of low_38_ok low_20

def G_42 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def R_42 : List Nat := varsOf 39
lemma low_42_ok : carryOK [(0,3),(0,4),(0,2),(0,1)] R_42 G_42 R_23 G_23 = true := by decide +kernel
lemma low_42 : Lower R_42 G_42 7 := carry_of low_42_ok low_23

def G_45 : Nat := 0xff88ff88ee88ee88ff88ff88ee88ee88
def R_45 : List Nat := varsOf 43
lemma low_45_ok : carryOK [(0,2),(0,1)] R_45 G_45 R_21 G_21 = true := by decide +kernel
lemma low_45 : Lower R_45 G_45 5 := carry_of low_45_ok low_21

def G_46 : Nat := 0xffa0ffa0faa0faa0ffa0ffa0faa0faa0
def R_46 : List Nat := varsOf 45
lemma low_46_ok : carryOK [(0,1)] R_46 G_46 R_21 G_21 = true := by decide +kernel
lemma low_46 : Lower R_46 G_46 5 := carry_of low_46_ok low_21

def G_53 : Nat := 0xfe80fe80e880e880fe80fe80e880e880
def R_53 : List Nat := varsOf 47
def pos_53 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,39,39,39,41,41,41,42,42,42,43,44,44,44,45,46,7,7,7,7,7,7,7,11,11,11,11,11,13,13,13,13,13,14,14,14,14,14,41,41,41,41,41,42,42,42,42,42,44,44,44,44,44]
def neg_53 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,38,37,35,40,33,9,40,34,10,35,40,36,12,37,38,9,10,12,35,37,38,40,12,35,37,38,40,10,35,37,38,40,9,35,37,38,40,10,12,35,37,38,9,12,35,37,38,9,10,35,37,38]
def fmask_53 : Nat := fullMask 64
def base_53 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3e0ffffa23f1ff,0x6b587318ca2361b6),(0xcccccccccccccccccccccccccccccccc,0x7c1f07ffc3c7e3f,0xb52aa5a954385c2d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf801ff83ffc07fc7,0xc6b4c635a7803b43),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffffffc07ff8ff8,0x18c718c6395686d8),(0xffffffff00000000ffffffff00000000,0xfffe000007fff000,0xe739ef7bc6edf000)]
def steps_53 : List (Nat × Nat × Nat) := [(2,0,1),(1,0,1),(0,0,1),(3,0,1),(3,7,6),(3,9,2),(2,9,2),(1,9,2),(0,9,2),(3,13,12)]
def W_53 : BT Decor := buildWiresBT 4 base_53 steps_53
def autosL_53 : List (List (Nat × Nat)) := [[],[(0,1)],[(1,2)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_53 : BT (List (Nat × Nat)) := btOfList 3 autosL_53
def slicesL_53 : List (Option (Nat × Nat)) := [some (subcubeFast 0 32,6),some (subcubeFast 32 2,4),some (subcubeFast 2 8,4),some (subcubeFast 0 2,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 4,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,7),some (subcubeFast 1 8,4),some (subcubeFast 32 0,7),some (subcubeFast 1 0,5)]
def slices_53 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_53
def ps_53 : List PoolSpec := [(0,[(0,0,1),(1,0,1),(3,7,6)]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(0,[]),(10,[]),(8,[(1,0,1)]),(11,[]),(10,[(0,0,1)])]
def P_53 : BT (Option BoundPool) := buildPoolsBT 4 W_53 R_53 slices_53 ps_53
lemma gp_53 : goodPairs G_53 pos_53 neg_53 := goodPairs_of (by decide +kernel)
lemma base_53_ok : ∀ x ∈ base_53, faithful pos_53 neg_53 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_53_ok : btAll (fun x => faithful pos_53 neg_53 x ∧ x.1 < 2^128) W_53 := buildWiresBT_faithful base_53_ok
set_option maxRecDepth 500000 in
lemma autos_53_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_53 = G_53) autos_53 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_53_0_ok : sliceDirectCheck 0 32 0 R_53 G_53 R_19 G_19 = true := by decide +kernel
lemma sl_53_0 : Slice R_53 G_53 (subcubeFast 0 32) 6 := slice_fast_direct sl_53_0_ok low_19
lemma sl_53_1_ok : sliceDirectCheck 32 2 0 R_53 G_53 R_5 G_5 = true := by decide +kernel
lemma sl_53_1 : Slice R_53 G_53 (subcubeFast 32 2) 4 := slice_fast_direct sl_53_1_ok low_5
lemma sl_53_2_ok : sliceDirectCheck 2 8 0 R_53 G_53 R_7 G_7 = true := by decide +kernel
lemma sl_53_2 : Slice R_53 G_53 (subcubeFast 2 8) 4 := slice_fast_direct sl_53_2_ok low_7
lemma sl_53_3_ok : sliceDirectCheck 0 2 0 R_53 G_53 R_46 G_46 = true := by decide +kernel
lemma sl_53_3 : Slice R_53 G_53 (subcubeFast 0 2) 5 := slice_fast_direct sl_53_3_ok low_46
lemma sl_53_4_ok : sliceDirectCheck 0 1 0 R_53 G_53 R_21 G_21 = true := by decide +kernel
lemma sl_53_4 : Slice R_53 G_53 (subcubeFast 0 1) 5 := slice_fast_direct sl_53_4_ok low_21
lemma sl_53_5_ok : sliceDirectCheck 2 0 0 R_53 G_53 R_33 G_33 = true := by decide +kernel
lemma sl_53_5 : Slice R_53 G_53 (subcubeFast 2 0) 5 := slice_fast_direct sl_53_5_ok low_33
lemma sl_53_6_ok : sliceDirectCheck 0 4 0 R_53 G_53 R_45 G_45 = true := by decide +kernel
lemma sl_53_6 : Slice R_53 G_53 (subcubeFast 0 4) 5 := slice_fast_direct sl_53_6_ok low_45
lemma sl_53_7_ok : sliceDirectCheck 4 0 0 R_53 G_53 R_28 G_28 = true := by decide +kernel
lemma sl_53_7 : Slice R_53 G_53 (subcubeFast 4 0) 5 := slice_fast_direct sl_53_7_ok low_28
lemma sl_53_8_ok : sliceDirectCheck 0 8 0 R_53 G_53 R_42 G_42 = true := by decide +kernel
lemma sl_53_8 : Slice R_53 G_53 (subcubeFast 0 8) 7 := slice_fast_direct sl_53_8_ok low_42
lemma sl_53_9_ok : sliceDirectCheck 1 8 0 R_53 G_53 R_10 G_10 = true := by decide +kernel
lemma sl_53_9 : Slice R_53 G_53 (subcubeFast 1 8) 4 := slice_fast_direct sl_53_9_ok low_10
lemma sl_53_10_ok : sliceDirectCheck 32 0 0 R_53 G_53 R_24 G_24 = true := by decide +kernel
lemma sl_53_10 : Slice R_53 G_53 (subcubeFast 32 0) 7 := slice_fast_direct sl_53_10_ok low_24
lemma sl_53_11_ok : sliceDirectCheck 1 0 0 R_53 G_53 R_38 G_38 = true := by decide +kernel
lemma sl_53_11 : Slice R_53 G_53 (subcubeFast 1 0) 5 := slice_fast_direct sl_53_11_ok low_38
set_option maxRecDepth 500000 in
lemma slices_53_ok : btAll (fun o => ∀ p, o = some p → Slice R_53 G_53 p.1 p.2) slices_53 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_53 G_53 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_53_0) (forall_cons (fun _ h => by cases h; exact sl_53_1) (forall_cons (fun _ h => by cases h; exact sl_53_2) (forall_cons (fun _ h => by cases h; exact sl_53_3) (forall_cons (fun _ h => by cases h; exact sl_53_4) (forall_cons (fun _ h => by cases h; exact sl_53_5) (forall_cons (fun _ h => by cases h; exact sl_53_6) (forall_cons (fun _ h => by cases h; exact sl_53_7) (forall_cons (fun _ h => by cases h; exact sl_53_8) (forall_cons (fun _ h => by cases h; exact sl_53_9) (forall_cons (fun _ h => by cases h; exact sl_53_10) (forall_cons (fun _ h => by cases h; exact sl_53_11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
set_option maxRecDepth 500000 in
lemma P_53_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_53 G_53 c) P_53 := buildPoolsBT_sound slices_53_ok
def bk_53_init : BT (List (List Nat)) := BT.empty
lemma bk_53_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 (0 - 1) xs.toFinset) bk_53_init := trivial
def nodes_53_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_0 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_init 0 nodes_53_0 = true := by decide +kernel
def bk_53_0 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_0
set_option maxRecDepth 500000 in
lemma bk_53_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 0 xs.toFinset) bk_53_0 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_init_ok chk_53_0
def nodes_53_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_1 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_0 1 nodes_53_1 = true := by decide +kernel
def bk_53_1 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_1
set_option maxRecDepth 500000 in
lemma bk_53_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 1 xs.toFinset) bk_53_1 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_0_ok chk_53_1
def nodes_53_2 : List NodeSpec := [([14,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_2 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_1 2 nodes_53_2 = true := by decide +kernel
def bk_53_2 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_2
set_option maxRecDepth 500000 in
lemma bk_53_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 2 xs.toFinset) bk_53_2 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_1_ok chk_53_2
def nodes_53_3 : List NodeSpec := nodesWithIdentity [([11,10,3,4],[]),([13,12,3,4],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_3 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_2 3 nodes_53_3 = true := by decide +kernel
def bk_53_3 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_3
set_option maxRecDepth 500000 in
lemma bk_53_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 3 xs.toFinset) bk_53_3 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_2_ok chk_53_3
def nodes_53_4 : List NodeSpec := nodesWithIdentity [([9,10,2,3,4],[]),([11,9,2,3,4],[]),([9,2,12,3,4],[]),([13,9,2,3,4],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_4 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_3 4 nodes_53_4 = true := by decide +kernel
def bk_53_4 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_4
set_option maxRecDepth 500000 in
lemma bk_53_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 4 xs.toFinset) bk_53_4 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_3_ok chk_53_4
def nodes_53_5 : List NodeSpec := nodesWithIdentity [([9,2,3,4],[2,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_5 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_4 5 nodes_53_5 = true := by decide +kernel
def bk_53_5 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_5
set_option maxRecDepth 500000 in
lemma bk_53_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 5 xs.toFinset) bk_53_5 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_4_ok chk_53_5
def nodes_53_6 : List NodeSpec := nodesWithIdentity [([5,8,2,3,4],[3,4,2,1]),([7,6,2,3,4],[5,4,2,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_6 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_5 6 nodes_53_6 = true := by decide +kernel
def bk_53_6 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_6
set_option maxRecDepth 500000 in
lemma bk_53_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 6 xs.toFinset) bk_53_6 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_5_ok chk_53_6
def nodes_53_7 : List NodeSpec := nodesWithIdentity [([5,0,1,2,3,4],[5,4,3,6,7,8,9,10,11,1]),([0,1,6,2,3,4],[4,5,3,7,6,12,11,10,1]),([7,0,1,2,3,4],[5,3,6,7,8,2,10,11,4,13,1,14])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_7 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_6 7 nodes_53_7 = true := by decide +kernel
def bk_53_7 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_7
set_option maxRecDepth 500000 in
lemma bk_53_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 7 xs.toFinset) bk_53_7 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_6_ok chk_53_7
def nodes_53_8 : List NodeSpec := [([0,1,2,3,4],[8,11],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_53_8 : checkNodesBT W_53 G_53 fmask_53 P_53 autos_53 bk_53_7 8 nodes_53_8 = true := by decide +kernel
def bk_53_8 : BT (List (List Nat)) := buildBucketsBT W_53 nodes_53_8
set_option maxRecDepth 500000 in
lemma bk_53_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_53 8 xs.toFinset) bk_53_8 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok P_53_ok autos_53_ok bk_53_7_ok chk_53_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_53_ok : forestRootCheck R_53 G_53 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 3,11,3),(VAR 5,41,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_53_in : bucketContainsBT bk_53_8 R_53 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_53 : Lower R_53 G_53 9 := lower_of_forestBT root_53_ok bk_53_8_ok root_53_in

end Cofactor12080
def h1R : List Nat := varsOf 31
def h1G : Nat := 0xeaa8e880eaa8e880eaa8e880eaa8e880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bound : Lower h1R h1G 9 := carry_of (swaps := [(4,5),(2,3),(1,2),(0,1)]) (roots2 := Cofactor12080.R_53) (T2 := Cofactor12080.G_53) (by decide +kernel) Cofactor12080.low_53
def h2R : List Nat := varsOf 47
def h2G : Nat := 0xeaa8eaa8e880e880eaa8eaa8e880e880
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 9 := carry_of (swaps := [(4,5)]) (roots2 := h1R) (T2 := h1G) (by decide +kernel) h1Bound
namespace Cofactor12058
def G_0 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def R_0 : List Nat := varsOf 52
def pos_0 : List Nat := [20,20,36,36,48,48,20,36,48]
def neg_0 : List Nat := [16,4,32,4,32,16,32,16,4]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 2,20,16),(VAR 4,20,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_6 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_6 : List Nat := varsOf 22
lemma low_6_ok : carryOK [(3,5),(1,3),(1,4),(1,2)] R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 4 := carry_of low_6_ok low_0

def G_7 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_7 : List Nat := varsOf 38
lemma low_7_ok : carryOK [(1,3),(1,4),(1,2)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0

def G_9 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def R_9 : List Nat := varsOf 50
lemma low_9_ok : carryOK [(1,2)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0

def G_11 : Nat := 0xff00f000f0000000ff00f000f0000000
def R_11 : List Nat := varsOf 60
lemma low_11_ok : liftCheck 0 8 R_11 G_11 R_0 G_0 [(VAR 3,28,20)] = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 5 := lift_of low_11_ok low_0

def G_12 : Nat := 0xfff0ff00ff00f000fff0ff00ff00f000
def R_12 : List Nat := varsOf 60
def pos_12 : List Nat := [12,12,24,24,28,40,40,44,52,52,52,56,12,12,12,24,24,24,40,40,40,52]
def neg_12 : List Nat := [8,4,16,8,20,32,8,36,48,36,20,48,20,36,48,20,36,48,20,36,48,8]
def fmask_12 : Nat := fullMask 22
def base_12 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x207793,0xdb692),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1ff8ff,0x200049),(0xffff0000ffff0000ffff0000ffff0000,0x238f1c,0x16dd14),(0xffffffff00000000ffffffff00000000,0x3c0fe0,0x1b6ba0)]
def steps_12 : List (Nat × Nat × Nat) := [(2,0,2),(1,0,2),(2,0,1),(0,0,2),(3,0,1),(1,0,1),(0,0,1),(3,0,2),(3,4,3),(2,9,2),(0,9,2),(1,4,3),(3,10,2),(1,10,2),(3,7,5)]
def W_12 : BT Decor := buildWiresBT 5 base_12 steps_12
def autosL_12 : List (List (Nat × Nat)) := [[],[(4,5)],[(2,4)],[(2,5),(2,4)],[(2,4),(2,5)],[(2,5)]]
def autos_12 : BT (List (Nat × Nat)) := btOfList 3 autosL_12
def slicesL_12 : List (Option (Nat × Nat)) := []
def slices_12 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_12
def ps_12 : List PoolSpec := []
def P_12 : BT (Option BoundPool) := buildPoolsBT 1 W_12 R_12 slices_12 ps_12
lemma gp_12 : goodPairs G_12 pos_12 neg_12 := goodPairs_of (by decide +kernel)
lemma base_12_ok : ∀ x ∈ base_12, faithful pos_12 neg_12 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_12_ok : btAll (fun x => faithful pos_12 neg_12 x ∧ x.1 < 2^128) W_12 := buildWiresBT_faithful base_12_ok
set_option maxRecDepth 500000 in
lemma autos_12_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_12 = G_12) autos_12 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_12_ok : btAll (fun o => ∀ p, o = some p → Slice R_12 G_12 p.1 p.2) slices_12 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_12 G_12 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_12_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_12 G_12 c) P_12 := buildPoolsBT_sound slices_12_ok
def bk_12_init : BT (List (List Nat)) := BT.empty
lemma bk_12_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 (0 - 1) xs.toFinset) bk_12_init := trivial
def nodes_12_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_0 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_init 0 nodes_12_0 = true := by decide +kernel
def bk_12_0 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_0
set_option maxRecDepth 500000 in
lemma bk_12_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 0 xs.toFinset) bk_12_0 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_init_ok chk_12_0
def nodes_12_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_1 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_0 1 nodes_12_1 = true := by decide +kernel
def bk_12_1 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_1
set_option maxRecDepth 500000 in
lemma bk_12_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 1 xs.toFinset) bk_12_1 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_0_ok chk_12_1
def nodes_12_2 : List NodeSpec := [([18,1,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_2 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_1 2 nodes_12_2 = true := by decide +kernel
def bk_12_2 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_2
set_option maxRecDepth 500000 in
lemma bk_12_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 2 xs.toFinset) bk_12_2 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_1_ok chk_12_2
def nodes_12_3 : List NodeSpec := [([4,11,1,3],[],[0]),([0,1,2,12],[],[]),([7,1,5,3],[],[0]),([13,0,1,3],[],[]),([0,1,14,3],[],[]),([6,8,2,3],[],[]),([0,1,2,15],[],[]),([16,0,1,3],[],[]),([0,1,17,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_3 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_2 3 nodes_12_3 = true := by decide +kernel
def bk_12_3 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_3
set_option maxRecDepth 500000 in
lemma bk_12_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 3 xs.toFinset) bk_12_3 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_2_ok chk_12_3
def nodes_12_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([0,1,2,5,3],[],[0]),([6,0,1,2,3],[],[0]),([7,0,1,2,3],[],[0]),([8,0,1,2,3],[],[0]),([0,1,9,2,3],[],[0,1]),([10,0,1,2,3],[],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_4 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_3 4 nodes_12_4 = true := by decide +kernel
def bk_12_4 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_4
set_option maxRecDepth 500000 in
lemma bk_12_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 4 xs.toFinset) bk_12_4 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_3_ok chk_12_4
def nodes_12_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_12_5 : checkNodesBT W_12 G_12 fmask_12 P_12 autos_12 bk_12_4 5 nodes_12_5 = true := by decide +kernel
def bk_12_5 : BT (List (List Nat)) := buildBucketsBT W_12 nodes_12_5
set_option maxRecDepth 500000 in
lemma bk_12_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_12 5 xs.toFinset) bk_12_5 :=
  buildBucketsBT_sound (by decide) gp_12 W_12_ok P_12_ok autos_12_ok bk_12_4_ok chk_12_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_ok : forestRootCheck R_12 G_12 [(VAR 2,12,8),(VAR 3,12,4),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_12_in : bucketContainsBT bk_12_5 R_12 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_12 : Lower R_12 G_12 6 := lower_of_forestBT root_12_ok bk_12_5_ok root_12_in

def G_13 : Nat := 0xfffffcfcfcfcc0c0fffffcfcfcfcc0c0
def R_13 : List Nat := varsOf 54
def pos_13 : List Nat := [6,6,18,18,20,20,34,34,36,36,48,48,6,6,18,18,20,20,34,34,36,36,48,48]
def neg_13 : List Nat := [4,2,16,2,16,4,32,2,32,4,32,16,16,32,4,32,2,32,4,16,2,16,2,4]
def fmask_13 : Nat := fullMask 24
def base_13 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf0cf,0x51008a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x333333,0x844221),(0xffff0000ffff0000ffff0000ffff0000,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def steps_13 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_13 : BT Decor := buildWiresBT 4 base_13 steps_13
def autosL_13 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_13 : BT (List (Nat × Nat)) := btOfList 4 autosL_13
def slicesL_13 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,4),some (subcubeFast 2 0,4),some (subcubeFast 32 0,4),some (subcubeFast 16 0,4)]
def slices_13 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_13
def ps_13 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_13 : BT (Option BoundPool) := buildPoolsBT 2 W_13 R_13 slices_13 ps_13
lemma gp_13 : goodPairs G_13 pos_13 neg_13 := goodPairs_of (by decide +kernel)
lemma base_13_ok : ∀ x ∈ base_13, faithful pos_13 neg_13 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_13_ok : btAll (fun x => faithful pos_13 neg_13 x ∧ x.1 < 2^128) W_13 := buildWiresBT_faithful base_13_ok
set_option maxRecDepth 500000 in
lemma autos_13_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_13 = G_13) autos_13 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_13_0_ok : sliceDirectCheck 4 0 0 R_13 G_13 R_9 G_9 = true := by decide +kernel
lemma sl_13_0 : Slice R_13 G_13 (subcubeFast 4 0) 4 := slice_fast_direct sl_13_0_ok low_9
lemma sl_13_1_ok : sliceDirectCheck 2 0 0 R_13 G_13 R_0 G_0 = true := by decide +kernel
lemma sl_13_1 : Slice R_13 G_13 (subcubeFast 2 0) 4 := slice_fast_direct sl_13_1_ok low_0
lemma sl_13_2_ok : sliceDirectCheck 32 0 0 R_13 G_13 R_6 G_6 = true := by decide +kernel
lemma sl_13_2 : Slice R_13 G_13 (subcubeFast 32 0) 4 := slice_fast_direct sl_13_2_ok low_6
lemma sl_13_3_ok : sliceDirectCheck 16 0 0 R_13 G_13 R_7 G_7 = true := by decide +kernel
lemma sl_13_3 : Slice R_13 G_13 (subcubeFast 16 0) 4 := slice_fast_direct sl_13_3_ok low_7
set_option maxRecDepth 500000 in
lemma slices_13_ok : btAll (fun o => ∀ p, o = some p → Slice R_13 G_13 p.1 p.2) slices_13 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_13 G_13 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_13_0) (forall_cons (fun _ h => by cases h; exact sl_13_1) (forall_cons (fun _ h => by cases h; exact sl_13_2) (forall_cons (fun _ h => by cases h; exact sl_13_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_13_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_13 G_13 c) P_13 := buildPoolsBT_sound slices_13_ok
def bk_13_init : BT (List (List Nat)) := BT.empty
lemma bk_13_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 (0 - 1) xs.toFinset) bk_13_init := trivial
def nodes_13_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_0 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_init 0 nodes_13_0 = true := by decide +kernel
def bk_13_0 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_0
set_option maxRecDepth 500000 in
lemma bk_13_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 0 xs.toFinset) bk_13_0 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_init_ok chk_13_0
def nodes_13_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_1 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_0 1 nodes_13_1 = true := by decide +kernel
def bk_13_1 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_1
set_option maxRecDepth 500000 in
lemma bk_13_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 1 xs.toFinset) bk_13_1 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_0_ok chk_13_1
def nodes_13_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_2 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_1 2 nodes_13_2 = true := by decide +kernel
def bk_13_2 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_2
set_option maxRecDepth 500000 in
lemma bk_13_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 2 xs.toFinset) bk_13_2 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_1_ok chk_13_2
def nodes_13_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_3 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_2 3 nodes_13_3 = true := by decide +kernel
def bk_13_3 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_3
set_option maxRecDepth 500000 in
lemma bk_13_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 3 xs.toFinset) bk_13_3 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_2_ok chk_13_3
def nodes_13_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_4 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_3 4 nodes_13_4 = true := by decide +kernel
def bk_13_4 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_4
set_option maxRecDepth 500000 in
lemma bk_13_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 4 xs.toFinset) bk_13_4 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_3_ok chk_13_4
def nodes_13_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_5 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_4 5 nodes_13_5 = true := by decide +kernel
def bk_13_5 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_5
set_option maxRecDepth 500000 in
lemma bk_13_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 5 xs.toFinset) bk_13_5 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_4_ok chk_13_5
def nodes_13_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_13_6 : checkNodesBT W_13 G_13 fmask_13 P_13 autos_13 bk_13_5 6 nodes_13_6 = true := by decide +kernel
def bk_13_6 : BT (List (List Nat)) := buildBucketsBT W_13 nodes_13_6
set_option maxRecDepth 500000 in
lemma bk_13_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_13 6 xs.toFinset) bk_13_6 :=
  buildBucketsBT_sound (by decide) gp_13 W_13_ok P_13_ok autos_13_ok bk_13_5_ok chk_13_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_ok : forestRootCheck R_13 G_13 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_13_in : bucketContainsBT bk_13_6 R_13 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_13 : Lower R_13 G_13 7 := lower_of_forestBT root_13_ok bk_13_6_ok root_13_in

def G_23 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
def R_23 : List Nat := varsOf 30
lemma low_23_ok : carryOK [(1,5),(1,4),(1,2)] R_23 G_23 R_11 G_11 = true := by decide +kernel
lemma low_23 : Lower R_23 G_23 5 := carry_of low_23_ok low_11

def G_24 : Nat := 0xfc00fc00c000c000fc00fc00c000c000
def R_24 : List Nat := varsOf 46
lemma low_24_ok : carryOK [(1,4),(1,2)] R_24 G_24 R_11 G_11 = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 5 := carry_of low_24_ok low_11

def G_29 : Nat := 0xff00cc00cc000000ff00cc00cc000000
def R_29 : List Nat := varsOf 58
lemma low_29_ok : carryOK [(1,2)] R_29 G_29 R_11 G_11 = true := by decide +kernel
lemma low_29 : Lower R_29 G_29 5 := carry_of low_29_ok low_11

def G_35 : Nat := 0xffc0fc00ffc0fc00ffc0fc00ffc0fc00
def R_35 : List Nat := varsOf 30
lemma low_35_ok : carryOK [(1,5),(1,4),(1,2)] R_35 G_35 R_12 G_12 = true := by decide +kernel
lemma low_35 : Lower R_35 G_35 6 := carry_of low_35_ok low_12

def G_36 : Nat := 0xffc0ffc0fc00fc00ffc0ffc0fc00fc00
def R_36 : List Nat := varsOf 46
lemma low_36_ok : carryOK [(1,4),(1,2)] R_36 G_36 R_12 G_12 = true := by decide +kernel
lemma low_36 : Lower R_36 G_36 6 := carry_of low_36_ok low_12

def G_37 : Nat := 0xffccff00ff00cc00ffccff00ff00cc00
def R_37 : List Nat := varsOf 58
lemma low_37_ok : carryOK [(1,2)] R_37 G_37 R_12 G_12 = true := by decide +kernel
lemma low_37 : Lower R_37 G_37 6 := carry_of low_37_ok low_12

def G_42 : Nat := 0xffc0fc00fc00c000ffc0fc00fc00c000
def R_42 : List Nat := varsOf 62
def pos_42 : List Nat := [14,14,14,26,26,26,28,28,28,30,42,42,42,44,44,44,46,54,54,54,54,56,56,56,58,60,14,14,14,14,14,14,26,26,26,26,26,26,28,28,28,28,28,28,42,42,42,42,42,42,44,44,44,44,44,44,54,54,54,54,56,56,56,56,56,56]
def neg_42 : List Nat := [12,10,6,24,18,10,24,20,12,22,40,34,10,40,36,12,38,52,50,38,22,48,40,24,50,52,22,24,38,40,50,52,12,22,38,40,50,52,10,22,38,40,50,52,12,22,24,38,50,52,10,22,24,38,50,52,10,12,24,40,10,12,22,38,50,52]
def fmask_42 : Nat := fullMask 66
def base_42 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xf03f03ffd1f1e3f,0x1d16da5d6551d1a36),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffc0fc0fe1fe3c7,0x2e2aab9a7961bc385),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f0ffffffffe1ffff,0x3f14524928c0b56b),(0xffff0000ffff0000ffff0000ffff0000,0x3ff000fff03fe03f8,0x344db6cb2cfb602d8),(0xffffffff00000000ffffffff00000000,0x3fffff00003fffc00,0x388e38f3cf36f6c00)]
def steps_42 : List (Nat × Nat × Nat) := [(0,0,1),(0,3,4),(1,5,6)]
def W_42 : BT Decor := buildWiresBT 3 base_42 steps_42
def autosL_42 : List (List (Nat × Nat)) := [[],[(2,4)],[(2,5),(2,4)],[(1,2),(1,4)],[(2,5),(1,2),(1,4)],[(2,5),(1,4)]]
def autos_42 : BT (List (Nat × Nat)) := btOfList 3 autosL_42
def slicesL_42 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,5),some (subcubeFast 32 0,5),some (subcubeFast 0 16,6),some (subcubeFast 16 0,5),some (subcubeFast 0 32,6),some (subcubeFast 0 2,6),some (subcubeFast 2 0,5),some (subcubeFast 0 4,6),some (subcubeFast 0 8,7),some (subcubeFast 4 8,4)]
def slices_42 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_42
def ps_42 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[(0,3,4)]),(6,[]),(7,[]),(4,[(0,0,1)]),(5,[]),(8,[]),(9,[]),(2,[(0,0,1)])]
def P_42 : BT (Option BoundPool) := buildPoolsBT 4 W_42 R_42 slices_42 ps_42
lemma gp_42 : goodPairs G_42 pos_42 neg_42 := goodPairs_of (by decide +kernel)
lemma base_42_ok : ∀ x ∈ base_42, faithful pos_42 neg_42 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_42_ok : btAll (fun x => faithful pos_42 neg_42 x ∧ x.1 < 2^128) W_42 := buildWiresBT_faithful base_42_ok
set_option maxRecDepth 500000 in
lemma autos_42_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_42 = G_42) autos_42 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_42_0_ok : sliceDirectCheck 4 0 0 R_42 G_42 R_29 G_29 = true := by decide +kernel
lemma sl_42_0 : Slice R_42 G_42 (subcubeFast 4 0) 5 := slice_fast_direct sl_42_0_ok low_29
lemma sl_42_1_ok : sliceDirectCheck 32 0 0 R_42 G_42 R_23 G_23 = true := by decide +kernel
lemma sl_42_1 : Slice R_42 G_42 (subcubeFast 32 0) 5 := slice_fast_direct sl_42_1_ok low_23
lemma sl_42_2_ok : sliceDirectCheck 0 16 0 R_42 G_42 R_36 G_36 = true := by decide +kernel
lemma sl_42_2 : Slice R_42 G_42 (subcubeFast 0 16) 6 := slice_fast_direct sl_42_2_ok low_36
lemma sl_42_3_ok : sliceDirectCheck 16 0 0 R_42 G_42 R_24 G_24 = true := by decide +kernel
lemma sl_42_3 : Slice R_42 G_42 (subcubeFast 16 0) 5 := slice_fast_direct sl_42_3_ok low_24
lemma sl_42_4_ok : sliceDirectCheck 0 32 0 R_42 G_42 R_35 G_35 = true := by decide +kernel
lemma sl_42_4 : Slice R_42 G_42 (subcubeFast 0 32) 6 := slice_fast_direct sl_42_4_ok low_35
lemma sl_42_5_ok : sliceDirectCheck 0 2 0 R_42 G_42 R_12 G_12 = true := by decide +kernel
lemma sl_42_5 : Slice R_42 G_42 (subcubeFast 0 2) 6 := slice_fast_direct sl_42_5_ok low_12
lemma sl_42_6_ok : sliceDirectCheck 2 0 0 R_42 G_42 R_11 G_11 = true := by decide +kernel
lemma sl_42_6 : Slice R_42 G_42 (subcubeFast 2 0) 5 := slice_fast_direct sl_42_6_ok low_11
lemma sl_42_7_ok : sliceDirectCheck 0 4 0 R_42 G_42 R_37 G_37 = true := by decide +kernel
lemma sl_42_7 : Slice R_42 G_42 (subcubeFast 0 4) 6 := slice_fast_direct sl_42_7_ok low_37
lemma sl_42_8_ok : sliceDirectCheck 0 8 0 R_42 G_42 R_13 G_13 = true := by decide +kernel
lemma sl_42_8 : Slice R_42 G_42 (subcubeFast 0 8) 7 := slice_fast_direct sl_42_8_ok low_13
lemma sl_42_9_ok : sliceDirectCheck 4 8 0 R_42 G_42 R_9 G_9 = true := by decide +kernel
lemma sl_42_9 : Slice R_42 G_42 (subcubeFast 4 8) 4 := slice_fast_direct sl_42_9_ok low_9
set_option maxRecDepth 500000 in
lemma slices_42_ok : btAll (fun o => ∀ p, o = some p → Slice R_42 G_42 p.1 p.2) slices_42 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_42 G_42 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_42_0) (forall_cons (fun _ h => by cases h; exact sl_42_1) (forall_cons (fun _ h => by cases h; exact sl_42_2) (forall_cons (fun _ h => by cases h; exact sl_42_3) (forall_cons (fun _ h => by cases h; exact sl_42_4) (forall_cons (fun _ h => by cases h; exact sl_42_5) (forall_cons (fun _ h => by cases h; exact sl_42_6) (forall_cons (fun _ h => by cases h; exact sl_42_7) (forall_cons (fun _ h => by cases h; exact sl_42_8) (forall_cons (fun _ h => by cases h; exact sl_42_9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 500000 in
lemma P_42_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_42 G_42 c) P_42 := buildPoolsBT_sound slices_42_ok
def bk_42_init : BT (List (List Nat)) := BT.empty
lemma bk_42_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 (0 - 1) xs.toFinset) bk_42_init := trivial
def nodes_42_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_0 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_init 0 nodes_42_0 = true := by decide +kernel
def bk_42_0 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_0
set_option maxRecDepth 500000 in
lemma bk_42_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 0 xs.toFinset) bk_42_0 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_init_ok chk_42_0
def nodes_42_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_1 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_0 1 nodes_42_1 = true := by decide +kernel
def bk_42_1 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_1
set_option maxRecDepth 500000 in
lemma bk_42_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 1 xs.toFinset) bk_42_1 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_0_ok chk_42_1
def nodes_42_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_2 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_1 2 nodes_42_2 = true := by decide +kernel
def bk_42_2 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_2
set_option maxRecDepth 500000 in
lemma bk_42_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 2 xs.toFinset) bk_42_2 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_1_ok chk_42_2
def nodes_42_3 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_3 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_2 3 nodes_42_3 = true := by decide +kernel
def bk_42_3 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_3
set_option maxRecDepth 500000 in
lemma bk_42_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 3 xs.toFinset) bk_42_3 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_2_ok chk_42_3
def nodes_42_4 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_4 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_3 4 nodes_42_4 = true := by decide +kernel
def bk_42_4 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_4
set_option maxRecDepth 500000 in
lemma bk_42_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 4 xs.toFinset) bk_42_4 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_3_ok chk_42_4
def nodes_42_5 : List NodeSpec := [([0,1,2,3,7,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_5 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_4 5 nodes_42_5 = true := by decide +kernel
def bk_42_5 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_5
set_option maxRecDepth 500000 in
lemma bk_42_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 5 xs.toFinset) bk_42_5 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_4_ok chk_42_5
def nodes_42_6 : List NodeSpec := nodesWithIdentity [([5,0,1,2,6,3,4],[0,1,2,3,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_6 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_5 6 nodes_42_6 = true := by decide +kernel
def bk_42_6 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_6
set_option maxRecDepth 500000 in
lemma bk_42_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 6 xs.toFinset) bk_42_6 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_5_ok chk_42_6
def nodes_42_7 : List NodeSpec := nodesWithIdentity [([5,0,1,2,3,4],[7,9,0,10,11,2,3,4,1,8,12])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_7 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_6 7 nodes_42_7 = true := by decide +kernel
def bk_42_7 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_7
set_option maxRecDepth 500000 in
lemma bk_42_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 7 xs.toFinset) bk_42_7 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_6_ok chk_42_7
def nodes_42_8 : List NodeSpec := [([0,1,2,3,4],[9,7,10,2,4],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_42_8 : checkNodesBT W_42 G_42 fmask_42 P_42 autos_42 bk_42_7 8 nodes_42_8 = true := by decide +kernel
def bk_42_8 : BT (List (List Nat)) := buildBucketsBT W_42 nodes_42_8
set_option maxRecDepth 500000 in
lemma bk_42_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_42 8 xs.toFinset) bk_42_8 :=
  buildBucketsBT_sound (by decide) gp_42 W_42_ok P_42_ok autos_42_ok bk_42_7_ok chk_42_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_ok : forestRootCheck R_42 G_42 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 4,26,10),(VAR 5,42,10)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_42_in : bucketContainsBT bk_42_8 R_42 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_42 : Lower R_42 G_42 9 := lower_of_forestBT root_42_ok bk_42_8_ok root_42_in

end Cofactor12058
def h3R : List Nat := varsOf 55
def h3G : Nat := 0xeaeaa8a8a8a88080eaeaa8a8a8a88080
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 9 := carry_of (swaps := [(0,1),(1,2),(2,3),(1,2),(0,1)]) (roots2 := Cofactor12058.R_42) (T2 := Cofactor12058.G_42) (by decide +kernel) Cofactor12058.low_42
def h4R : List Nat := varsOf 59
def h4G : Nat := 0xeeaaaa88aa888800eeaaaa88aa888800
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 9 := carry_of (swaps := [(2,3)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h5R : List Nat := varsOf 60
def h5G : Nat := 0xfffffff0fff0f000fffffff0fff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 7 := carry_of (swaps := [(2,3),(1,2)]) (roots2 := Cofactor12058.R_13) (T2 := Cofactor12058.G_13) (by decide +kernel) Cofactor12058.low_13
namespace Cofactor12168
def G_0 : Nat := 0xffffff00ff000000ffffff00ff000000
def R_0 : List Nat := varsOf 56
def pos_0 : List Nat := [24,24,40,40,48,48,24,40,48]
def neg_0 : List Nat := [16,8,32,8,32,16,32,16,8]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xff00ff00ff00ff00ff00ff00ff00ff00,0xcf,0x10a),(0xffff0000ffff0000ffff0000ffff0000,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 3,24,16),(VAR 4,24,8),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(2,5),(1,4),(0,3)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0

def G_3 : Nat := 0xeeeeeeee88888888eeeeeeee88888888
def R_3 : List Nat := varsOf 35
lemma low_3_ok : carryOK [(1,2),(0,2),(1,4),(0,3)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0

def G_5 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def R_5 : List Nat := varsOf 37
lemma low_5_ok : carryOK [(2,4),(0,1),(0,3)] R_5 G_5 R_0 G_0 = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 4 := carry_of low_5_ok low_0

def G_7 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_7 : List Nat := varsOf 38
lemma low_7_ok : carryOK [(2,4),(1,3)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0

def G_10 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def R_10 : List Nat := varsOf 39
def pos_10 : List Nat := [3,3,5,5,6,6,33,33,34,34,36,36,3,3,5,5,6,6,33,33,34,34,36,36]
def neg_10 : List Nat := [2,1,4,1,4,2,32,1,32,2,32,4,4,32,2,32,1,32,2,4,1,4,1,2]
def fmask_10 : Nat := fullMask 24
def base_10 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def steps_10 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_10 : BT Decor := buildWiresBT 4 base_10 steps_10
def autosL_10 : List (List (Nat × Nat)) := [[],[(2,5)],[(0,1)],[(2,5),(0,1)],[(1,2)],[(1,5),(1,2)],[(0,1),(0,2)],[(1,5),(0,1),(0,2)],[(1,5),(0,2)]]
def autos_10 : BT (List (Nat × Nat)) := btOfList 4 autosL_10
def slicesL_10 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 1 0,4),some (subcubeFast 32 0,4),some (subcubeFast 4 0,4)]
def slices_10 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_10
def ps_10 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_10 : BT (Option BoundPool) := buildPoolsBT 2 W_10 R_10 slices_10 ps_10
lemma gp_10 : goodPairs G_10 pos_10 neg_10 := goodPairs_of (by decide +kernel)
lemma base_10_ok : ∀ x ∈ base_10, faithful pos_10 neg_10 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_10_ok : btAll (fun x => faithful pos_10 neg_10 x ∧ x.1 < 2^128) W_10 := buildWiresBT_faithful base_10_ok
set_option maxRecDepth 500000 in
lemma autos_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_10 = G_10) autos_10 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_10_0_ok : sliceDirectCheck 2 0 0 R_10 G_10 R_5 G_5 = true := by decide +kernel
lemma sl_10_0 : Slice R_10 G_10 (subcubeFast 2 0) 4 := slice_fast_direct sl_10_0_ok low_5
lemma sl_10_1_ok : sliceDirectCheck 1 0 0 R_10 G_10 R_7 G_7 = true := by decide +kernel
lemma sl_10_1 : Slice R_10 G_10 (subcubeFast 1 0) 4 := slice_fast_direct sl_10_1_ok low_7
lemma sl_10_2_ok : sliceDirectCheck 32 0 0 R_10 G_10 R_1 G_1 = true := by decide +kernel
lemma sl_10_2 : Slice R_10 G_10 (subcubeFast 32 0) 4 := slice_fast_direct sl_10_2_ok low_1
lemma sl_10_3_ok : sliceDirectCheck 4 0 0 R_10 G_10 R_3 G_3 = true := by decide +kernel
lemma sl_10_3 : Slice R_10 G_10 (subcubeFast 4 0) 4 := slice_fast_direct sl_10_3_ok low_3
set_option maxRecDepth 500000 in
lemma slices_10_ok : btAll (fun o => ∀ p, o = some p → Slice R_10 G_10 p.1 p.2) slices_10 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_10 G_10 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_10_0) (forall_cons (fun _ h => by cases h; exact sl_10_1) (forall_cons (fun _ h => by cases h; exact sl_10_2) (forall_cons (fun _ h => by cases h; exact sl_10_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_10_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_10 G_10 c) P_10 := buildPoolsBT_sound slices_10_ok
def bk_10_init : BT (List (List Nat)) := BT.empty
lemma bk_10_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 (0 - 1) xs.toFinset) bk_10_init := trivial
def nodes_10_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_0 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_init 0 nodes_10_0 = true := by decide +kernel
def bk_10_0 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_0
set_option maxRecDepth 500000 in
lemma bk_10_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 0 xs.toFinset) bk_10_0 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_init_ok chk_10_0
def nodes_10_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_1 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_0 1 nodes_10_1 = true := by decide +kernel
def bk_10_1 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_1
set_option maxRecDepth 500000 in
lemma bk_10_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 1 xs.toFinset) bk_10_1 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_0_ok chk_10_1
def nodes_10_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_2 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_1 2 nodes_10_2 = true := by decide +kernel
def bk_10_2 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_2
set_option maxRecDepth 500000 in
lemma bk_10_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 2 xs.toFinset) bk_10_2 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_1_ok chk_10_2
def nodes_10_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_3 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_2 3 nodes_10_3 = true := by decide +kernel
def bk_10_3 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_3
set_option maxRecDepth 500000 in
lemma bk_10_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 3 xs.toFinset) bk_10_3 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_2_ok chk_10_3
def nodes_10_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_4 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_3 4 nodes_10_4 = true := by decide +kernel
def bk_10_4 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_4
set_option maxRecDepth 500000 in
lemma bk_10_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 4 xs.toFinset) bk_10_4 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_3_ok chk_10_4
def nodes_10_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_5 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_4 5 nodes_10_5 = true := by decide +kernel
def bk_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_5
set_option maxRecDepth 500000 in
lemma bk_10_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 5 xs.toFinset) bk_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_4_ok chk_10_5
def nodes_10_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_10_6 : checkNodesBT W_10 G_10 fmask_10 P_10 autos_10 bk_10_5 6 nodes_10_6 = true := by decide +kernel
def bk_10_6 : BT (List (List Nat)) := buildBucketsBT W_10 nodes_10_6
set_option maxRecDepth 500000 in
lemma bk_10_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_10 6 xs.toFinset) bk_10_6 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok P_10_ok autos_10_ok bk_10_5_ok chk_10_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck R_10 G_10 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 5,33,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT bk_10_6 R_10 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_10 : Lower R_10 G_10 7 := lower_of_forestBT root_10_ok bk_10_6_ok root_10_in

def G_32 : Nat := 0xfe00fe00e800e800fe00fe00e800e800
def R_32 : List Nat := varsOf 47
lemma low_32_ok : liftCheck 0 8 R_32 G_32 R_10 G_10 [(VAR 3,11,3)] = true := by decide +kernel
lemma low_32 : Lower R_32 G_32 8 := lift_of low_32_ok low_10

end Cofactor12168
def h6R : List Nat := varsOf 61
def h6G : Nat := 0xaaaaaaa0aaa0a000aaaaaaa0aaa0a000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 8 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := Cofactor12168.R_32) (T2 := Cofactor12168.G_32) (by decide +kernel) Cofactor12168.low_32
def h8R : List Nat := varsOf 15
def h8G : Nat := 0xeaa8eaa8eaa8eaa8eaa8eaa8eaa8eaa8
def h8Pos : List Nat := [5,14,5,9,3,5,14,9,14,3,3,3,5,3,9,7,7,11,11,13,13]
def h8Neg : List Nat := [4,12,6,8,2,1,10,1,6,1,0,6,0,10,0,6,1,10,1,12,1]
def h8Mask : Nat := fullMask 21
def h8Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1ffebd,0x1502a0),(0xcccccccccccccccccccccccccccccccc,0x7af52,0x2a954),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x199167,0x88907),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1e41ca,0xa204a)]
def h8Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,1,3),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(1,2,4),(0,1,28),(2,2,4),(1,3,4),(0,1,31),(2,3,4),(0,2,5),(1,1,34),(3,2,5),(0,3,5),(1,1,37),(3,3,5),(2,1,8),(1,3,8),(0,2,41),(2,3,8),(3,1,9),(0,3,9),(1,2,45),(3,3,9),(2,1,12),(2,2,12),(3,1,13),(3,2,13),(1,3,18),(0,1,52),(2,3,18),(1,2,54),(1,3,19),(0,2,56),(2,3,19),(1,1,58),(1,2,22),(0,1,60),(2,2,23),(1,1,62)]
def h8W : BT Decor := buildWiresBT 6 h8Base h8Steps
def h8AutoList : List (List (Nat × Nat)) := [[]]
def h8Autos : BT (List (Nat × Nat)) := btOfList 1 h8AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Pairs : goodPairs h8G h8Pos h8Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8BaseOk : ∀ x ∈ h8Base, faithful h8Pos h8Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8WOk : btAll (fun x => faithful h8Pos h8Neg x ∧ x.1 < 2^128) h8W := buildWiresBT_faithful h8BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h8G = h8G) h8Autos := btAll_ofList (autos_of (by decide +kernel))
def h8SliceList : List (Option (Nat × Nat)) := []
def h8Slices : BT (Option (Nat × Nat)) := btOfList 1 h8SliceList
def h8Specs : List PoolSpec := []
def h8Pools : BT (Option BoundPool) := buildPoolsBT 1 h8W h8R h8Slices h8Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h8R h8G p.1 p.2) h8Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h8R h8G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h8R h8G c) h8Pools := buildPoolsBT_sound h8SlicesOk
def h8Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h8G (3 - 1) xs.toFinset) h8Empty := trivial
def h8Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,3,28],[]),([0,1,3,30],[]),([0,1,2,31],[]),([0,1,2,33],[]),([0,1,3,34],[]),([0,1,3,36],[]),([0,1,2,37],[]),([0,1,2,39],[]),([0,2,3,35],[]),([0,2,3,40],[]),([0,1,2,41],[]),([0,1,2,43],[]),([0,2,3,29],[]),([0,2,3,44],[]),([0,1,2,45],[]),([0,1,2,47],[]),([0,2,3,38],[]),([0,2,3,48],[]),([0,1,3,46],[]),([0,1,3,49],[]),([0,2,3,32],[]),([0,2,3,50],[]),([0,1,3,42],[]),([0,1,3,51],[]),([0,3,16,17],[]),([0,1,2,52],[]),([0,1,2,54],[]),([0,1,2,56],[]),([0,1,2,58],[]),([0,2,20,21],[]),([0,1,3,60],[]),([0,1,3,57],[]),([0,1,3,55],[]),([0,1,3,62],[]),([0,1,24,25],[]),([0,2,3,63],[]),([0,2,3,53],[]),([0,2,3,59],[]),([0,2,3,61],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Test3_0 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Empty 3 h8Block3_0 = true := by decide +kernel
def h8Nodes3 : List NodeSpec := h8Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Check3 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Empty 3 h8Nodes3 = true := h8Test3_0
def h8Bucket3 : BT (List (List Nat)) := buildBucketsBT h8W h8Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h8G 3 xs.toFinset) h8Bucket3 := buildBucketsBT_sound (by decide) h8Pairs h8WOk h8PoolsOk h8AutosOk h8EmptyOk h8Check3
def h8Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[]),([0,1,2,3,5],[]),([0,1,2,3,6],[]),([0,1,2,3,7],[]),([0,1,2,3,8],[]),([0,1,2,3,9],[]),([0,1,2,3,10],[]),([0,1,2,3,11],[]),([0,1,2,3,12],[]),([0,1,2,3,13],[]),([0,1,2,3,14],[]),([0,1,2,3,15],[]),([0,1,2,3,16],[]),([0,1,2,3,17],[]),([0,1,2,3,18],[]),([0,1,2,3,19],[]),([0,1,2,3,20],[]),([0,1,2,3,21],[]),([0,1,2,3,22],[]),([0,1,2,3,23],[]),([0,1,2,3,24],[]),([0,1,2,3,25],[]),([0,1,2,3,26],[]),([0,1,2,3,27],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Test4_0 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Bucket3 4 h8Block4_0 = true := by decide +kernel
def h8Nodes4 : List NodeSpec := h8Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Check4 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Bucket3 4 h8Nodes4 = true := h8Test4_0
def h8Bucket4 : BT (List (List Nat)) := buildBucketsBT h8W h8Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h8G 4 xs.toFinset) h8Bucket4 := buildBucketsBT_sound (by decide) h8Pairs h8WOk h8PoolsOk h8AutosOk h8Bucket3Ok h8Check4
def h8Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Test5_0 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Bucket4 5 h8Block5_0 = true := by decide +kernel
def h8Nodes5 : List NodeSpec := h8Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Check5 : checkNodesBT h8W h8G h8Mask h8Pools h8Autos h8Bucket4 5 h8Nodes5 = true := h8Test5_0
def h8Bucket5 : BT (List (List Nat)) := buildBucketsBT h8W h8Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h8G 5 xs.toFinset) h8Bucket5 := buildBucketsBT_sound (by decide) h8Pairs h8WOk h8PoolsOk h8AutosOk h8Bucket4Ok h8Check5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 6 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)]) (by decide +kernel) h8Bucket5Ok (by decide +kernel)
def h9R : List Nat := varsOf 23
def h9G : Nat := 0xeaeaa8a8eaeaa8a8eaeaa8a8eaeaa8a8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 6 := carry_of (swaps := [(3,4)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h10R : List Nat := varsOf 27
def h10G : Nat := 0xeeaaaa88eeaaaa88eeaaaa88eeaaaa88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 6 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h11R : List Nat := varsOf 28
def h11G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def h11Pos : List Nat := [20,24,12,12,24,20]
def h11Neg : List Nat := [16,16,4,8,8,4]
def h11Mask : Nat := fullMask 6
def h11Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,45,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,30,24),(0xffff0000ffff0000ffff0000ffff0000,51,3)]
def h11Steps : List (Nat × Nat × Nat) := []
def h11W : BT Decor := buildWiresBT 2 h11Base h11Steps
def h11AutoList : List (List (Nat × Nat)) := [[]]
def h11Autos : BT (List (Nat × Nat)) := btOfList 1 h11AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Pairs : goodPairs h11G h11Pos h11Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11BaseOk : ∀ x ∈ h11Base, faithful h11Pos h11Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11WOk : btAll (fun x => faithful h11Pos h11Neg x ∧ x.1 < 2^128) h11W := buildWiresBT_faithful h11BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h11G = h11G) h11Autos := btAll_ofList (autos_of (by decide +kernel))
def h11SliceList : List (Option (Nat × Nat)) := []
def h11Slices : BT (Option (Nat × Nat)) := btOfList 1 h11SliceList
def h11Specs : List PoolSpec := []
def h11Pools : BT (Option BoundPool) := buildPoolsBT 1 h11W h11R h11Slices h11Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h11R h11G p.1 p.2) h11Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h11R h11G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h11R h11G c) h11Pools := buildPoolsBT_sound h11SlicesOk
def h11Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G (3 - 1) xs.toFinset) h11Empty := trivial
def h11Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Test3_0 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 3 h11Block3_0 = true := by decide +kernel
def h11Nodes3 : List NodeSpec := h11Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Check3 : checkNodesBT h11W h11G h11Mask h11Pools h11Autos h11Empty 3 h11Nodes3 = true := h11Test3_0
def h11Bucket3 : BT (List (List Nat)) := buildBucketsBT h11W h11Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h11G 3 xs.toFinset) h11Bucket3 := buildBucketsBT_sound (by decide) h11Pairs h11WOk h11PoolsOk h11AutosOk h11EmptyOk h11Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 4 := lower_of_forestBT (essPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 4,4,20)]) (by decide +kernel) h11Bucket3Ok (by decide +kernel)
def h12R : List Nat := varsOf 30
def h12G : Nat := 0xccc0c000ccc0c000ccc0c000ccc0c000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 5 := lift_of (z := 0) (o := 2) (essPairs := [(VAR 1,12,14)]) (by decide +kernel) h11Bound
def h13R : List Nat := varsOf 29
def h13G : Nat := 0xfffafaaafffafaaafffafaaafffafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h11Bound
def h7R : List Nat := varsOf 31
def h7G : Nat := 0xeeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8
def h7Pos : List Nat := [5,14,5,9,14,5,14,9,22,17,17,3,26,22,3,26,22,26,7,9,13,21,11,25,19,26,22,14,3,7,11,19,22,14,26,14,26,22,7,11,19,3,13,9,5,17,14,21,17,5,9,22,17,13,25,17,9,5,26,3,13,3,21,14,22,26,30,30,30,30]
def h7Neg : List Nat := [4,12,6,8,10,1,6,1,6,1,16,2,24,20,1,10,18,18,6,10,1,1,10,1,18,28,28,28,0,1,1,1,16,8,16,4,8,4,2,2,2,6,12,12,12,28,2,20,20,20,28,2,18,8,24,24,24,28,2,10,4,18,4,0,0,0,18,10,6,28]
def h7Mask : Nat := fullMask 70
def h7Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7bf7bfc0f1fc4ead,0xe0b042a0),(0xcccccccccccccccccccccccccccccccc,0x3fac0843ffff47f952,0x1c2c1843c0014f8954),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3dd22ad46b2c352177,0x305207be280e042147),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3e95644c9e4ada90da,0x280be43c120e48901a),(0xffff0000ffff0000ffff0000ffff0000,0x3f44d9a13587a3b700,0x2423d7a0050f033400)]
def h7Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(1,0,2),(2,0,2),(1,0,3),(2,0,3),(1,0,4),(2,0,4),(0,1,2),(1,1,2),(2,1,2),(0,1,3),(1,1,3),(2,1,3),(0,1,4),(1,1,4),(2,1,4),(0,2,3),(1,2,3),(0,0,25),(1,0,25),(2,0,25),(3,0,25),(0,1,25),(1,0,30),(3,0,30),(2,2,3),(3,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(1,2,5),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(1,3,39),(3,3,39),(1,4,30),(3,4,30),(1,4,39),(3,4,39),(1,30,39),(1,3,5),(3,2,51),(1,4,51),(3,4,51),(1,30,51),(1,4,5),(3,2,56),(3,3,56),(1,5,30),(3,2,59),(3,3,59),(1,1,25),(2,1,25),(3,1,25),(0,1,39),(2,1,39),(1,4,25),(3,4,25),(0,1,51),(2,1,51),(0,1,56),(2,1,56),(2,1,44),(3,5,25),(2,1,74),(0,0,36),(1,0,36),(2,0,36),(3,0,36),(0,1,36),(1,0,80),(3,0,80),(1,3,80),(3,3,80),(1,39,80),(1,56,80),(1,5,80),(3,2,87),(3,4,87),(1,1,36),(2,1,36),(3,1,36),(3,3,36),(2,1,48),(3,5,36),(2,1,95),(0,0,41),(1,0,41),(2,0,41),(3,0,41),(0,1,41),(1,0,101),(3,0,101),(1,1,41),(2,1,41),(3,1,41),(2,1,45),(2,1,49),(1,2,101),(3,2,101),(1,51,101),(1,56,101),(1,5,101),(3,3,113),(3,4,113),(3,2,41),(2,1,53),(3,5,41),(2,1,118),(2,1,52),(2,1,54),(2,1,57),(2,1,58),(1,0,17),(3,3,6),(1,3,17),(3,4,6),(1,4,17),(2,6,17),(0,6,25),(1,17,130),(2,6,25),(0,6,36),(1,17,133),(2,6,36),(3,2,6),(1,0,126),(3,0,126),(3,2,126),(1,4,126),(3,4,126),(1,0,63),(1,2,63),(1,4,63),(1,2,144),(3,2,144),(3,3,144),(2,4,63),(3,4,63),(2,6,63),(1,0,128),(3,0,128),(3,2,128),(1,0,91),(1,2,91),(1,3,91),(1,2,156),(3,2,156),(2,3,91),(2,6,91),(1,2,129),(1,0,20),(1,4,20),(2,6,20),(1,0,143),(3,0,143),(3,3,143),(3,4,143),(0,6,41),(1,20,169),(2,6,41),(1,0,163),(3,0,163),(3,3,163),(1,0,105),(1,2,105),(3,3,176),(2,2,105),(1,3,105),(2,6,105),(1,3,164),(1,0,23),(2,6,23),(1,0,155),(3,0,155),(3,4,155),(1,0,179),(3,0,179),(3,4,179),(1,4,183),(1,3,136),(1,4,136),(1,2,125),(1,4,125),(1,2,127),(1,3,127),(1,3,161),(3,3,161),(1,4,161),(3,4,161),(3,2,181),(1,4,181),(3,4,181),(3,1,197),(3,4,197),(1,0,205),(3,0,205),(2,1,205),(3,7,25),(3,2,190),(3,3,190),(3,1,199),(3,3,199),(1,0,213),(3,0,213),(2,1,213),(3,7,36),(3,1,202),(3,2,202),(1,0,219),(3,0,219),(2,1,219),(3,7,41),(3,3,124),(3,4,124),(1,8,63),(1,8,91),(3,2,162),(3,4,162),(1,8,105),(3,2,182),(3,3,182),(1,3,66),(1,4,66),(1,2,70),(1,4,70),(1,4,73),(1,2,72),(1,3,72),(1,3,94),(1,2,117),(0,4,9),(3,4,9),(0,4,11),(3,4,11),(0,9,11),(0,2,11),(3,2,11),(0,3,9),(3,3,9),(1,3,248),(1,4,248),(3,4,248),(1,2,250),(1,4,250),(3,4,250),(0,4,27),(1,4,27),(3,4,27),(1,2,259),(1,3,259),(0,3,13),(3,3,13),(0,9,13),(0,2,13),(3,2,13),(1,3,266),(3,3,266),(1,4,266),(1,2,243),(0,3,77),(3,3,77),(1,2,272),(2,9,20),(2,9,23),(1,4,26),(1,4,29),(0,25,41),(0,25,77),(0,41,77),(0,9,41),(1,25,243),(3,0,67),(0,1,67),(0,9,67),(1,3,76),(1,3,79),(0,36,41),(0,27,36),(0,27,41),(1,36,250),(0,1,258),(3,2,258),(1,2,221),(3,2,255),(3,2,261),(1,4,251),(3,4,251),(3,3,269),(0,1,297),(3,10,41),(0,11,13),(1,4,263),(1,3,245),(0,2,98),(2,11,17),(2,11,23),(0,25,36),(0,25,98),(0,36,98),(0,11,36),(3,3,260),(3,4,254),(0,1,291),(3,12,36),(2,13,17),(2,13,20),(0,13,25),(0,1,282),(3,14,25),(1,4,167),(3,4,167),(1,3,186),(0,16,41),(1,4,64),(3,17,41),(3,25,128),(3,17,67),(1,3,92),(3,36,126),(1,2,141),(1,2,147),(1,4,139),(0,19,36),(3,20,36),(1,3,146),(0,22,25),(3,23,25),(3,26,27),(1,4,75),(3,4,31),(3,30,62),(3,76,77),(1,3,96),(3,3,81),(3,80,90),(3,97,98),(1,40,285),(3,40,293),(1,2,119),(3,2,102),(3,101,104),(1,40,328)]
def h7W : BT Decor := buildWiresBT 9 h7Base h7Steps
def h7AutoList : List (List (Nat × Nat)) := [[]]
def h7Autos : BT (List (Nat × Nat)) := btOfList 1 h7AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Pairs : goodPairs h7G h7Pos h7Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7BaseOk : ∀ x ∈ h7Base, faithful h7Pos h7Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7WOk : btAll (fun x => faithful h7Pos h7Neg x ∧ x.1 < 2^128) h7W := buildWiresBT_faithful h7BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h7G = h7G) h7Autos := btAll_ofList (autos_of (by decide +kernel))
def h7SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 16 0,6)]
def h7Slices : BT (Option (Nat × Nat)) := btOfList 3 h7SliceList
def h7Specs : List PoolSpec := [(1,[]),(0,[]),(3,[(0,0,1)]),(4,[(0,0,1)]),(5,[(0,0,1)]),(2,[]),(0,[(1,2,5)]),(4,[]),(3,[]),(0,[(1,3,5)]),(0,[(1,4,5)]),(3,[(0,0,1),(1,4,5)]),(5,[(1,2,3)]),(3,[(0,0,1),(1,3,39)]),(3,[(0,0,1),(3,5,25)]),(5,[]),(3,[(0,0,1),(1,3,5)]),(4,[(1,2,4)]),(3,[(0,0,1),(1,4,39)]),(3,[(0,0,1),(3,5,36)]),(4,[(0,0,1),(1,2,5)]),(5,[(0,0,1),(1,2,5)]),(3,[(1,3,4)]),(4,[(0,0,1),(1,4,51)]),(4,[(0,0,1),(3,5,41)]),(5,[(0,0,1),(1,3,5)]),(4,[(0,0,1),(1,4,5)]),(3,[(1,0,1)]),(4,[(1,0,1)]),(5,[(1,0,1)]),(1,[(2,1,2)]),(1,[(2,1,3)]),(1,[(2,1,4)]),(3,[(1,0,1),(3,4,6)]),(3,[(1,0,1),(0,6,25)]),(3,[(1,0,1),(2,6,25)]),(3,[(1,0,1),(3,3,6)]),(3,[(1,0,1),(0,6,36)]),(3,[(1,0,1),(2,6,36)]),(1,[(3,2,6)]),(4,[(1,0,1),(3,2,6)]),(5,[(1,0,1),(3,2,6)]),(4,[(1,0,1),(2,6,25)]),(5,[(1,0,1),(2,6,36)]),(4,[(1,0,1),(0,6,41)]),(4,[(1,0,1),(2,6,41)]),(1,[(3,3,6)]),(5,[(1,0,1),(3,3,6)]),(5,[(1,0,1),(2,6,41)]),(1,[(3,4,6)]),(4,[(1,0,1),(3,4,6)]),(3,[(2,0,1)]),(4,[(2,0,1)]),(5,[(2,0,1)]),(3,[(3,0,1)]),(4,[(3,0,1)]),(5,[(3,0,1)]),(0,[(1,0,17)]),(0,[(1,0,20)]),(0,[(1,0,23)]),(1,[(2,1,39)]),(1,[(2,1,51)]),(1,[(2,1,56)]),(4,[(1,0,2)]),(5,[(1,0,2)]),(1,[(0,1,39)]),(0,[(1,0,2)]),(4,[(1,0,2),(3,4,9)]),(5,[(1,0,2),(3,3,9)]),(4,[(1,0,2),(0,9,41)]),(4,[(1,0,2),(3,4,250)]),(3,[(1,0,25)]),(5,[(1,0,3),(3,2,11)]),(4,[(1,0,25)]),(3,[(3,3,9)]),(3,[(1,0,36)]),(4,[(1,0,4),(3,2,13)]),(5,[(1,0,36)]),(3,[(3,4,9)]),(4,[(2,0,2)]),(5,[(2,0,2)]),(3,[(1,0,3)]),(4,[(3,2,11)]),(3,[(1,0,4)]),(5,[(3,2,13)]),(5,[(1,0,3)]),(1,[(0,1,51)]),(0,[(1,0,3)]),(3,[(1,0,3),(3,4,11)]),(3,[(1,0,3),(0,11,36)]),(3,[(1,0,3),(3,4,248)]),(4,[(1,0,41)]),(5,[(1,0,41)]),(3,[(1,0,4),(3,3,13)]),(4,[(3,4,11)]),(3,[(2,0,3)]),(5,[(2,0,3)]),(4,[(1,0,4)]),(5,[(3,3,13)]),(1,[(0,1,56)]),(3,[(1,0,4),(0,13,25)]),(3,[(1,0,4),(3,3,266)]),(0,[(1,0,4)]),(3,[(2,0,4)]),(4,[(2,0,4)]),(4,[(1,1,2)]),(5,[(1,1,2)]),(3,[(2,1,25)]),(3,[(2,1,36)]),(4,[(2,1,2)]),(5,[(2,1,2)]),(3,[(1,0,17)]),(4,[(2,1,2),(1,4,17)]),(5,[(2,1,2),(1,3,17)]),(4,[(2,1,2),(1,4,126)]),(4,[(2,1,2),(3,17,41)]),(3,[(1,3,17)]),(4,[(2,1,25)]),(3,[(0,1,25)]),(3,[(1,4,17)]),(5,[(2,1,36)]),(3,[(0,1,36)]),(3,[(1,1,3)]),(5,[(1,1,3)]),(4,[(2,1,41)]),(3,[(2,1,3)]),(5,[(2,1,3)]),(4,[(1,0,20)]),(3,[(2,1,3),(1,4,20)]),(3,[(2,1,25),(1,4,63)]),(3,[(2,1,3),(3,20,36)]),(4,[(0,1,25)]),(4,[(1,4,20)]),(5,[(2,1,41)]),(4,[(0,1,41)]),(3,[(1,1,4)]),(4,[(1,1,4)]),(3,[(2,1,4)]),(4,[(2,1,4)]),(5,[(1,0,23)]),(3,[(2,1,36),(1,3,91)]),(3,[(2,1,4),(3,23,25)]),(5,[(0,1,36)]),(5,[(0,1,41)]),(3,[(0,0,25)]),(3,[(0,0,25),(1,4,26)]),(3,[(1,0,25),(3,4,27)]),(3,[(2,0,25)]),(3,[(3,0,25)]),(4,[(3,0,25)]),(3,[(0,1,25),(1,1,25)]),(3,[(1,1,25)]),(3,[(3,1,25)]),(3,[(3,1,25),(1,4,64)]),(3,[(1,4,25)]),(4,[(1,4,25)]),(3,[(3,4,25)]),(4,[(3,4,25)]),(3,[(0,0,36)]),(3,[(0,0,36),(1,3,76)]),(3,[(1,0,36),(3,3,77)]),(3,[(2,0,36)]),(3,[(3,0,36)]),(5,[(3,0,36)]),(3,[(0,1,36),(1,1,36)]),(3,[(1,1,36)]),(3,[(3,1,36)]),(3,[(3,1,36),(1,3,92)]),(3,[(3,3,36)]),(5,[(3,3,36)]),(4,[(0,0,41)]),(4,[(2,0,41)]),(4,[(3,0,41)]),(5,[(3,0,41)]),(4,[(0,1,41),(1,1,41)]),(4,[(1,1,41)]),(4,[(2,1,41),(1,2,105)]),(4,[(3,1,41)]),(4,[(3,2,41)]),(5,[(3,2,41)])]
def h7Pools : BT (Option BoundPool) := buildPoolsBT 8 h7W h7R h7Slices h7Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Slice5 : Slice h7R h7G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Slice4 : Slice h7R h7G (subcubeFast 8 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Slice3 : Slice h7R h7G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Slice2 : Slice h7R h7G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Slice1 : Slice h7R h7G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Slice0 : Slice h7R h7G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h7R h7G p.1 p.2) h7Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h7R h7G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h7Slice0) (forall_cons (fun _ h => by cases h; exact h7Slice1) (forall_cons (fun _ h => by cases h; exact h7Slice2) (forall_cons (fun _ h => by cases h; exact h7Slice3) (forall_cons (fun _ h => by cases h; exact h7Slice4) (forall_cons (fun _ h => by cases h; exact h7Slice5) (fun _ h => (List.not_mem_nil h).elim)))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h7R h7G c) h7Pools := buildPoolsBT_sound h7SlicesOk
def h7Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G (3 - 1) xs.toFinset) h7Empty := trivial
def h7Block3_0 : List NodeSpec := nodesWithIdentity [([0,25,41,87],[]),([0,36,41,59],[]),([0,2,59,280],[]),([0,2,87,290],[]),([0,25,36,113],[]),([0,3,59,310],[]),([0,3,113,289],[]),([0,4,87,309],[]),([0,4,113,279],[]),([4,25,131,246],[]),([0,25,131,288],[]),([0,25,226,288],[]),([0,25,59,288],[]),([0,25,204,288],[]),([3,36,134,264],[]),([0,36,134,278],[]),([0,36,227,278],[]),([0,36,87,278],[]),([0,36,212,278],[]),([2,41,170,302],[]),([0,41,170,308],[]),([0,41,230,308],[]),([0,1,41,348],[]),([0,41,113,308],[]),([0,41,218,308],[]),([0,1,41,349],[]),([0,1,41,353],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test3_0 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Block3_0 = true := by decide +kernel
def h7Nodes3 : List NodeSpec := h7Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Check3 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Empty 3 h7Nodes3 = true := h7Test3_0
def h7Bucket3 : BT (List (List Nat)) := buildBucketsBT h7W h7Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G 3 xs.toFinset) h7Bucket3 := buildBucketsBT_sound (by decide) h7Pairs h7WOk h7PoolsOk h7AutosOk h7EmptyOk h7Check3
def h7Block4_0 : List NodeSpec := nodesWithIdentity [([0,3,4,30,39],[]),([0,2,4,30,51],[]),([0,2,3,30,56],[]),([0,2,3,4,59],[]),([0,3,4,39,80],[]),([0,2,4,51,80],[]),([0,2,3,56,80],[]),([0,2,3,4,87],[]),([0,3,4,39,101],[]),([0,3,4,39,59],[]),([0,3,4,39,87],[]),([0,2,4,51,101],[]),([0,2,3,56,101],[]),([0,2,3,4,113],[]),([0,2,4,51,59],[]),([0,2,4,51,113],[]),([0,2,3,56,87],[]),([0,2,3,56,113],[]),([0,3,4,17,130],[]),([0,3,4,17,133],[]),([0,2,3,6,144],[]),([0,2,3,4,150],[]),([0,2,4,6,156],[]),([0,2,3,4,160],[]),([0,2,4,20,130],[]),([0,2,4,20,169],[]),([0,3,4,6,176],[]),([0,2,3,4,180],[]),([0,2,3,23,133],[]),([0,2,3,23,169],[]),([0,1,2,3,205],[]),([0,1,2,4,213],[]),([0,1,3,4,219],[]),([0,2,3,8,144],[]),([0,2,4,8,156],[]),([0,3,4,8,176],[]),([0,1,2,3,237],[]),([0,1,2,4,240],[]),([0,1,3,4,241],[]),([0,1,2,3,259],[]),([0,1,2,4,272],[]),([0,1,4,25,274],[]),([0,1,3,36,275],[]),([0,4,18,25,65],[]),([0,3,21,36,65],[]),([0,1,25,41,77],[7]),([0,1,4,25,281],[7]),([0,3,4,25,87],[]),([0,1,27,36,41],[15]),([0,1,3,36,281],[15]),([0,3,4,36,59],[]),([0,2,4,41,59],[]),([0,2,3,41,87],[]),([0,2,3,4,292],[]),([0,1,3,4,293],[]),([0,3,4,37,59],[]),([0,2,4,42,59],[]),([0,3,4,59,248],[]),([0,2,4,59,250],[]),([0,2,3,59,257],[]),([0,2,3,59,259],[]),([0,2,3,204,257],[]),([0,2,3,204,259],[]),([0,1,3,248,257],[]),([0,1,2,250,257],[]),([0,2,4,59,249],[]),([0,3,4,33,87],[]),([0,2,3,43,87],[]),([0,3,4,87,266],[]),([0,2,4,87,271],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test4_0 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket3 4 h7Block4_0 = true := by decide +kernel
def h7Block4_1 : List NodeSpec := nodesWithIdentity [([0,2,4,87,272],[]),([0,2,3,87,243],[]),([0,2,4,212,271],[]),([0,2,4,212,272],[]),([0,1,4,266,271],[]),([0,1,2,243,271],[]),([0,2,3,87,242],[]),([0,2,3,4,300],[]),([0,1,4,25,306],[]),([0,1,2,41,307],[]),([0,4,15,25,69],[]),([0,2,21,41,69],[]),([0,1,25,36,98],[8]),([0,1,4,25,311],[8]),([0,2,4,25,113],[]),([0,1,2,41,311],[15]),([0,2,3,36,113],[]),([0,3,4,59,247],[]),([0,2,4,34,113],[]),([0,2,3,38,113],[]),([0,3,4,113,305],[]),([0,3,4,113,293],[]),([0,2,4,113,263],[]),([0,2,3,113,245],[]),([0,3,4,218,305],[]),([0,3,4,218,293],[]),([0,1,4,263,305],[]),([0,1,3,245,305],[]),([0,2,3,113,244],[]),([0,2,3,4,314],[]),([0,1,3,36,316],[]),([0,1,2,41,317],[]),([0,3,15,36,71],[]),([0,2,18,41,71],[]),([0,1,3,36,318],[8]),([0,1,2,41,318],[7]),([0,3,4,87,265],[]),([0,2,4,113,262],[]),([0,2,3,4,319],[]),([0,1,3,4,176],[]),([0,1,2,3,144],[]),([0,1,2,4,156],[]),([0,4,17,25,101],[]),([0,1,25,41,91],[7]),([0,1,4,25,326],[7]),([0,3,17,36,101],[]),([0,1,36,41,63],[15]),([0,1,3,36,326],[15]),([0,2,4,30,126],[]),([0,3,4,30,143],[]),([0,2,3,30,144],[]),([0,1,3,143,148],[]),([0,1,2,126,148],[]),([0,2,3,80,128],[]),([0,3,4,80,155],[]),([0,2,4,80,156],[]),([0,1,4,155,159],[]),([0,1,2,128,159],[]),([0,4,20,25,80],[]),([0,1,25,36,105],[8]),([0,1,4,25,335],[8]),([0,2,20,41,80],[]),([0,1,2,41,335],[15]),([0,1,38,41,143],[]),([0,2,3,101,163],[]),([0,3,4,101,176],[]),([0,2,4,101,179],[]),([0,1,4,178,179],[]),([0,1,3,163,178],[]),([0,3,23,30,36],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test4_1 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket3 4 h7Block4_1 = true := by decide +kernel
def h7Block4_2 : List NodeSpec := nodesWithIdentity [([0,2,23,30,41],[]),([0,1,3,36,338],[8]),([0,1,2,41,338],[7]),([0,1,33,36,179],[]),([0,1,34,41,155],[]),([1,2,3,4,339],[]),([0,4,24,25,131],[]),([0,4,24,25,226],[]),([0,4,24,25,59],[]),([0,4,24,25,204],[]),([0,1,2,3,340],[]),([0,1,29,36,41],[]),([0,1,2,3,341],[]),([0,1,30,36,41],[]),([0,2,3,4,342],[]),([0,2,3,64,144],[]),([0,1,25,41,79],[]),([0,1,25,41,80],[]),([0,1,25,36,100],[]),([0,1,25,36,101],[]),([1,2,3,4,343],[]),([0,3,35,36,134],[]),([0,3,35,36,227],[]),([0,3,35,36,87],[]),([0,3,35,36,212],[]),([0,1,2,4,344],[]),([0,1,2,4,345],[]),([0,2,3,4,346],[]),([0,2,4,92,156],[]),([1,2,3,4,347],[]),([0,2,40,41,170],[]),([0,2,40,41,230],[]),([0,1,40,41,285],[]),([0,2,40,41,113],[]),([0,2,40,41,218],[]),([0,1,40,41,293],[]),([0,1,3,4,350],[]),([0,1,3,4,351],[]),([0,2,3,4,352],[]),([0,3,4,106,176],[]),([0,1,40,41,328],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test4_2 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket3 4 h7Block4_2 = true := by decide +kernel
def h7Nodes4 : List NodeSpec := h7Block4_0 ++ h7Block4_1 ++ h7Block4_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Check4 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket3 4 h7Nodes4 = true := by
  unfold h7Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h7Test4_0,h7Test4_1⟩,h7Test4_2⟩
def h7Bucket4 : BT (List (List Nat)) := buildBucketsBT h7W h7Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G 4 xs.toFinset) h7Bucket4 := buildBucketsBT_sound (by decide) h7Pairs h7WOk h7PoolsOk h7AutosOk h7Bucket3Ok h7Check4
def h7Block5_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,5,30],[]),([0,1,3,4,25,39],[6,7]),([0,1,2,4,25,51],[8,9]),([0,1,2,3,25,56],[10,11]),([0,1,2,3,4,44],[13]),([0,1,2,3,4,74],[7,8,14]),([0,2,3,4,5,80],[]),([0,1,3,4,36,39],[6,15]),([0,1,2,4,36,51],[9,16]),([0,1,2,3,36,56],[8,10]),([0,1,2,3,4,48],[18]),([0,1,2,3,4,95],[8,15,19]),([0,1,3,4,39,41],[6,20]),([0,1,3,4,39,44],[6,20]),([0,1,3,4,39,45],[]),([0,1,3,4,39,48],[6,21]),([0,1,3,4,39,49],[]),([0,1,2,3,4,45],[0]),([0,1,2,3,4,49],[0]),([0,2,3,4,5,101],[]),([0,1,2,4,41,51],[9,15]),([0,1,2,3,41,56],[7,10]),([0,1,2,3,4,53],[23]),([0,1,2,3,4,118],[7,15,24]),([0,1,2,4,44,51],[9,13]),([0,1,2,4,51,52],[]),([0,1,2,4,51,53],[9,25]),([0,1,2,4,51,54],[]),([0,1,2,3,4,52],[0]),([0,1,2,3,4,54],[0]),([0,1,2,3,48,56],[10,18]),([0,1,2,3,56,57],[]),([0,1,2,3,53,56],[10,23]),([0,1,2,3,56,58],[]),([0,1,2,3,4,57],[0]),([0,1,2,3,4,58],[0]),([0,3,4,6,17,25],[]),([0,3,4,6,17,36],[]),([0,2,3,4,6,126],[]),([0,2,3,4,6,63],[]),([0,2,3,4,6,128],[]),([0,2,3,4,6,91],[]),([0,2,3,4,17,129],[8]),([0,2,4,6,20,25],[]),([0,2,3,4,6,143],[]),([0,2,4,6,20,41],[]),([0,2,3,4,6,163],[]),([0,2,3,4,6,105],[]),([0,2,3,4,20,164],[7]),([0,2,3,6,23,36],[]),([0,2,3,4,6,155],[]),([0,2,3,6,23,41],[]),([0,2,3,4,6,179],[]),([0,2,3,4,23,183],[15]),([0,1,3,4,25,136],[7]),([0,1,2,4,25,125],[8]),([0,1,2,3,25,127],[33]),([0,1,2,3,4,130],[0,7,8,34]),([0,1,2,3,4,132],[35]),([0,1,3,4,36,136],[15]),([0,1,2,4,36,125],[36]),([0,1,2,3,36,127],[8]),([0,1,2,3,4,133],[0,8,15,37]),([0,1,2,3,4,135],[38]),([0,1,3,4,41,136],[40]),([0,1,3,4,136,191],[]),([0,1,3,4,132,136],[42]),([0,1,3,4,136,192],[]),([0,1,3,4,135,136],[43]),([0,1,2,3,4,191],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test5_0 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Block5_0 = true := by decide +kernel
def h7Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,192],[1]),([0,1,2,4,41,125],[15]),([0,1,2,3,41,127],[7]),([0,1,2,3,4,169],[0,7,15,44]),([0,1,2,3,4,171],[45]),([0,1,2,4,125,193],[]),([0,1,2,4,125,132],[35]),([0,1,2,4,125,194],[]),([0,1,2,4,125,171],[48]),([0,1,2,3,4,193],[1]),([0,1,2,3,4,194],[1]),([0,1,2,3,127,195],[]),([0,1,2,3,127,135],[38]),([0,1,2,3,127,196],[]),([0,1,2,3,127,171],[45]),([0,1,2,3,4,195],[1]),([0,1,2,3,4,196],[1]),([0,2,3,4,7,30],[]),([0,1,3,4,25,161],[7]),([0,1,2,4,25,181],[8]),([0,1,2,3,4,197],[1,15]),([0,1,2,3,4,209],[]),([0,2,3,4,7,80],[]),([0,1,3,4,36,161],[15]),([0,1,2,3,36,190],[8]),([0,1,2,3,4,199],[1,7]),([0,1,2,3,4,217],[]),([0,1,3,4,33,161],[]),([0,1,3,4,37,161],[]),([0,1,2,3,4,198],[]),([0,1,2,3,4,200],[]),([0,2,3,4,7,101],[]),([0,1,2,4,41,181],[15]),([0,1,2,3,41,190],[7]),([0,1,2,3,4,202],[1,8]),([0,1,2,3,4,223],[]),([0,1,2,4,34,181],[]),([0,1,2,3,4,201],[]),([0,1,2,4,42,181],[]),([0,1,2,3,4,203],[]),([0,1,2,3,38,190],[]),([0,1,2,3,4,210],[]),([0,1,2,3,43,190],[]),([0,1,2,3,4,211],[]),([2,3,4,8,17,124],[57]),([0,3,4,8,17,25],[]),([0,3,4,8,17,36],[]),([0,2,3,4,8,126],[]),([0,2,3,4,8,63],[0]),([0,2,3,4,8,128],[]),([0,2,3,4,8,91],[0]),([2,3,4,8,20,162],[58]),([0,2,4,8,20,25],[]),([0,2,3,4,8,143],[]),([0,2,4,8,20,41],[]),([0,2,3,4,8,163],[]),([0,2,3,4,8,105],[0]),([2,3,4,8,23,182],[59]),([0,2,3,8,23,36],[]),([0,2,3,4,8,155],[]),([0,2,3,8,23,41],[]),([0,2,3,4,8,179],[]),([0,1,3,4,25,66],[7]),([0,1,2,4,25,70],[8]),([0,1,2,3,4,32],[]),([0,1,2,3,4,73],[15]),([0,1,3,4,36,66],[15]),([0,1,2,3,36,72],[8]),([0,1,2,3,4,82],[]),([0,1,2,3,4,94],[7])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test5_1 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Block5_1 = true := by decide +kernel
def h7Block5_2 : List NodeSpec := nodesWithIdentity [([1,2,3,4,66,124],[8]),([0,2,3,4,65,66],[8]),([0,1,3,4,33,66],[]),([0,1,3,4,37,66],[]),([0,1,2,3,4,233],[]),([0,1,2,3,4,234],[]),([0,1,2,4,41,70],[15]),([0,1,2,3,41,72],[7]),([0,1,2,3,4,103],[]),([0,1,2,3,4,117],[8]),([1,2,3,4,70,162],[8]),([0,2,3,4,69,70],[8]),([0,1,2,4,34,70],[]),([0,1,2,3,4,235],[]),([0,1,2,4,42,70],[]),([0,1,2,3,4,236],[]),([1,2,3,4,72,182],[8]),([0,2,3,4,71,72],[8]),([0,1,2,3,38,72],[]),([0,1,2,3,4,238],[]),([0,1,2,3,43,72],[]),([0,1,2,3,4,239],[]),([0,1,4,9,11,25],[7,8]),([0,1,3,4,9,248],[8]),([0,1,2,4,11,250],[8]),([0,1,2,3,4,27],[1,15]),([0,1,3,9,13,36],[8,15]),([0,1,3,4,9,266],[8]),([0,1,2,3,13,243],[8]),([0,1,2,3,4,77],[1,7]),([0,1,4,9,20,25],[7,8]),([0,1,3,4,9,143],[0]),([0,1,2,4,20,250],[1]),([0,1,2,3,4,61],[0]),([0,1,2,3,4,165],[1]),([0,1,2,3,4,274],[]),([0,1,3,9,23,36],[8,15]),([0,1,3,4,9,155],[0]),([0,1,2,3,23,243],[1]),([0,1,2,3,4,89],[0]),([0,1,2,3,4,184],[1]),([0,1,2,3,4,275],[]),([0,2,3,4,18,65],[]),([0,2,3,4,21,65],[]),([0,1,3,4,25,65],[6,7]),([0,1,3,4,36,65],[6,15]),([0,1,2,3,4,55],[]),([0,1,2,3,4,86],[]),([1,2,3,4,9,124],[8]),([1,3,4,9,25,26],[]),([1,3,4,9,25,29],[]),([0,1,4,9,25,41],[]),([0,1,4,9,25,250],[7]),([0,1,3,4,25,77],[7]),([0,1,3,4,25,243],[7,67]),([0,1,3,4,9,67],[0]),([0,1,3,4,9,68],[]),([1,3,4,9,36,76],[]),([1,3,4,9,36,79],[]),([0,1,3,9,36,41],[]),([0,1,3,4,27,36],[15]),([0,1,3,4,36,250],[15,68]),([0,1,3,4,9,93],[]),([0,1,3,9,36,243],[15]),([0,1,2,4,27,41],[15]),([0,1,2,3,41,77],[7]),([0,1,2,3,4,281],[0,7,15,69]),([0,1,2,3,4,258],[1]),([0,1,2,3,4,256],[70]),([0,1,2,3,4,221],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test5_2 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Block5_2 = true := by decide +kernel
def h7Block5_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,29],[]),([1,2,3,4,27,29],[8]),([0,2,3,4,59],[]),([0,1,2,3,4,59],[]),([0,2,3,4,27,59],[1]),([0,2,3,4,27,204],[]),([0,1,2,3,4,248],[]),([0,1,3,4,27,248],[8,72]),([0,1,2,3,4,250],[]),([0,1,2,4,27,250],[8,68]),([0,1,2,3,27,257],[]),([0,1,2,3,259],[]),([0,1,2,3,4,259],[]),([0,1,2,3,27,259],[15]),([1,2,3,4,9,29],[8]),([0,2,3,4,9,59],[]),([0,1,2,3,9,259],[]),([0,1,2,3,4,107],[]),([0,1,2,3,4,255],[]),([0,1,2,3,4,79],[]),([1,2,3,4,77,79],[8]),([0,2,3,4,87],[]),([0,1,2,3,4,87],[]),([0,2,3,4,77,87],[1]),([0,2,3,4,77,212],[]),([0,1,2,3,4,266],[]),([0,1,3,4,77,266],[8,76]),([0,1,2,4,77,271],[]),([0,1,2,4,272],[]),([0,1,2,3,4,272],[]),([0,1,2,4,77,272],[7]),([0,1,2,3,4,243],[]),([0,1,2,3,77,243],[8,67]),([1,2,3,4,9,79],[8]),([0,2,3,4,9,87],[]),([0,1,2,4,9,272],[]),([0,1,2,3,4,108],[]),([0,1,2,3,4,261],[]),([0,1,3,4,10,116],[]),([0,1,2,4,41,251],[15]),([0,1,2,3,41,269],[7]),([0,1,2,3,4,297],[1]),([0,1,2,3,4,301],[]),([0,1,2,3,4,298],[]),([0,1,2,3,4,299],[]),([0,1,2,11,13,41],[7,15]),([0,1,2,4,11,263],[8]),([0,1,2,3,13,245],[8]),([0,1,2,3,4,98],[1,8]),([0,1,4,11,17,25],[7,8]),([0,1,3,4,17,248],[1]),([0,1,2,4,11,126],[0]),([0,1,2,3,4,60],[0]),([0,1,2,3,4,137],[1]),([0,1,2,3,4,306],[]),([0,1,2,11,23,41],[7,15]),([0,1,2,4,11,179],[0]),([0,1,2,3,23,245],[1]),([0,1,2,3,4,115],[0]),([0,1,2,3,4,187],[1]),([0,1,2,3,4,307],[]),([0,2,3,4,15,69],[]),([0,2,3,4,21,69],[]),([0,1,2,4,25,69],[8,9]),([0,1,2,3,4,50],[]),([0,1,2,4,41,69],[9,15]),([0,1,2,3,4,112],[]),([1,2,3,4,11,162],[8]),([1,2,4,11,25,26],[]),([1,2,4,11,25,29],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test5_3 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Block5_3 = true := by decide +kernel
def h7Block5_4 : List NodeSpec := nodesWithIdentity [([0,1,4,11,25,36],[]),([0,1,4,11,25,248],[8]),([0,1,2,4,25,98],[8]),([0,1,2,4,25,245],[8,88]),([0,1,2,4,11,67],[0]),([0,1,2,4,11,68],[]),([0,1,2,11,36,41],[]),([0,1,2,3,36,98],[8]),([0,1,2,3,4,311],[0,8,15,89]),([0,1,2,3,4,253],[90]),([0,1,2,3,4,215],[]),([1,2,3,4,11,29],[8]),([0,2,3,4,11,59],[]),([0,1,2,3,11,259],[]),([0,1,2,3,4,120],[]),([0,1,2,4,41,248],[15,72]),([0,1,2,3,4,252],[]),([1,2,4,11,41,97],[]),([1,2,4,11,41,100],[]),([0,1,2,4,11,116],[]),([0,1,2,11,41,245],[15]),([0,1,2,3,4,100],[]),([1,2,3,4,98,100],[8]),([0,2,3,4,113],[]),([0,1,2,3,4,113],[]),([0,2,3,4,98,113],[1]),([0,2,3,4,98,218],[]),([0,1,3,4,98,305],[]),([0,1,3,4,293],[]),([0,1,2,3,4,293],[]),([0,1,3,4,98,293],[8]),([0,1,2,3,4,263],[]),([0,1,2,4,98,263],[8,93]),([0,1,2,3,4,245],[]),([0,1,2,3,98,245],[8,88]),([1,2,3,4,11,100],[8]),([0,2,3,4,11,113],[]),([0,1,3,4,11,293],[]),([0,1,2,3,4,121],[]),([0,1,2,3,4,260],[]),([0,1,3,4,36,254],[15]),([0,1,2,4,12,93],[]),([0,1,2,3,36,303],[8]),([0,1,2,3,4,291],[1]),([0,1,2,3,4,315],[]),([0,1,2,3,4,313],[]),([0,1,2,3,4,295],[]),([0,1,3,13,17,36],[8,15]),([0,1,3,4,17,266],[1]),([0,1,2,3,13,128],[0]),([0,1,2,3,4,88],[0]),([0,1,2,3,4,151],[1]),([0,1,2,3,4,316],[]),([0,1,2,13,20,41],[7,15]),([0,1,2,4,20,263],[1]),([0,1,2,3,13,163],[0]),([0,1,2,3,4,114],[0]),([0,1,2,3,4,172],[1]),([0,1,2,3,4,317],[]),([0,2,3,4,15,71],[]),([0,2,3,4,18,71],[]),([0,1,2,3,36,71],[8,10]),([0,1,2,3,4,85],[]),([0,1,2,3,41,71],[7,10]),([0,1,2,3,4,111],[]),([1,2,3,4,13,182],[8]),([0,1,3,13,25,36],[]),([0,1,2,13,25,41],[]),([0,1,2,3,13,67],[0]),([0,1,2,3,4,318],[0,7,8,100])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test5_4 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Block5_4 = true := by decide +kernel
def h7Block5_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,268],[101]),([0,1,2,3,4,207],[]),([1,2,3,13,36,76],[]),([1,2,3,13,36,79],[]),([0,1,3,13,36,266],[8]),([0,1,2,3,36,263],[8,93]),([0,1,2,3,13,93],[]),([1,2,3,4,13,79],[8]),([0,2,3,4,13,87],[]),([0,1,2,4,13,272],[]),([0,1,2,3,4,122],[]),([0,1,2,3,41,266],[7,76]),([0,1,2,3,4,267],[]),([1,2,3,13,41,97],[]),([1,2,3,13,41,100],[]),([0,1,2,3,13,116],[]),([0,1,2,13,41,263],[7]),([1,2,3,4,13,100],[8]),([0,2,3,4,13,113],[]),([0,1,3,4,13,293],[]),([0,1,2,3,4,123],[]),([0,1,2,3,4,273],[]),([0,1,3,4,25,270],[7]),([0,1,2,4,25,304],[8]),([0,1,2,3,14,68],[]),([0,1,2,3,4,282],[1]),([0,1,2,3,4,320],[]),([0,1,2,3,4,312],[]),([0,1,2,3,4,296],[]),([0,2,3,4,16,101],[]),([0,1,3,4,16,116],[]),([0,1,2,4,41,167],[15]),([0,1,2,3,41,186],[7]),([0,1,2,3,4,324],[]),([0,1,2,3,4,322],[8]),([0,1,2,3,4,143],[]),([0,1,2,3,4,63],[15]),([0,1,2,4,42,167],[]),([0,1,2,3,4,321],[]),([0,1,2,3,4,155],[]),([0,1,2,3,4,91],[7]),([0,1,2,3,43,186],[]),([0,1,2,3,4,323],[]),([0,1,3,4,25,124],[7]),([0,1,3,4,36,124],[15]),([0,1,2,3,4,224],[]),([0,1,2,3,4,225],[]),([0,2,3,4,17,65],[8]),([0,1,4,17,20,25],[7,8]),([0,1,3,4,17,143],[8]),([0,1,2,4,20,126],[8]),([0,1,3,17,23,36],[8,15]),([0,1,3,4,17,155],[8]),([0,1,2,3,23,128],[8]),([0,3,4,17,25,30],[]),([0,3,4,17,25,64],[]),([0,1,4,17,25,41],[]),([0,1,4,17,25,126],[7]),([0,1,3,4,25,128],[7,112]),([0,1,3,4,25,91],[7]),([0,1,3,4,17,67],[1]),([0,1,3,4,17,68],[]),([0,3,4,17,36,80],[]),([0,3,4,17,36,92],[]),([0,1,3,17,36,41],[]),([0,1,3,4,36,126],[15,113]),([0,1,3,4,36,63],[15]),([0,1,3,4,17,93],[]),([0,1,3,17,36,128],[15]),([0,2,3,4,17,101],[8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test5_5 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Block5_5 = true := by decide +kernel
def h7Block5_6 : List NodeSpec := nodesWithIdentity [([0,1,2,4,41,63],[15]),([0,1,2,3,41,91],[7]),([0,1,2,3,4,110],[]),([0,1,2,3,4,140],[8,114]),([0,1,2,3,4,149],[]),([0,1,2,3,4,326],[1,7,15,115]),([0,1,2,3,4,138],[]),([0,1,2,4,63,126],[8,113]),([0,1,2,3,4,141],[]),([0,1,2,3,4,142],[]),([0,1,2,3,4,30],[]),([0,2,3,4,30,63],[8]),([0,1,3,4,63,143],[8]),([0,1,2,3,4,126],[]),([0,1,2,3,144],[]),([0,1,2,3,4,144],[]),([0,1,2,3,63,144],[15]),([0,1,2,3,63,148],[]),([0,2,3,4,17,30],[8,118]),([0,1,2,3,17,144],[]),([0,1,2,3,4,152],[]),([0,1,2,3,4,147],[]),([0,1,2,3,91,128],[8,112]),([0,1,2,3,4,154],[]),([0,1,2,3,4,80],[]),([0,2,3,4,80,91],[8]),([0,1,3,4,91,155],[8]),([0,1,2,4,156],[]),([0,1,2,3,4,156],[]),([0,1,2,4,91,156],[7]),([0,1,2,4,91,159],[]),([0,1,2,3,4,128],[]),([0,2,3,4,17,80],[8,121]),([0,1,2,4,17,156],[]),([0,2,3,4,19,80],[]),([0,1,3,4,36,139],[15]),([0,1,2,4,19,93],[]),([0,1,2,3,36,189],[8]),([0,1,2,3,4,334],[]),([0,1,2,3,4,330],[7]),([0,1,2,3,4,333],[]),([0,1,2,3,38,189],[]),([0,1,2,3,4,331],[]),([0,1,2,3,4,179],[]),([0,1,2,3,4,105],[8]),([0,1,2,4,25,162],[8]),([0,1,2,3,4,228],[]),([0,1,2,4,41,162],[15]),([0,1,2,3,4,229],[]),([0,2,3,4,20,69],[8]),([0,1,2,20,23,41],[7,15]),([0,1,2,4,20,179],[8]),([0,1,2,3,23,163],[8]),([0,2,4,20,25,30],[]),([0,2,4,20,25,64],[]),([0,1,4,20,25,36],[]),([0,1,4,20,25,143],[8]),([0,1,2,4,25,163],[8,128]),([0,1,2,4,25,105],[8]),([0,1,2,4,20,67],[1]),([0,1,2,4,20,68],[]),([0,2,3,4,20,80],[7]),([0,1,2,20,36,41],[]),([0,1,2,3,36,105],[8]),([0,1,2,3,4,84],[]),([0,1,2,3,4,145],[7,129]),([0,1,2,3,4,335],[1,8,15,130]),([0,1,2,3,4,166],[]),([0,1,3,4,25,143],[8]),([0,1,3,4,38,143],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test5_6 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Block5_6 = true := by decide +kernel
def h7Block5_7 : List NodeSpec := nodesWithIdentity [([0,1,2,4,41,143],[15]),([0,1,2,4,42,143],[]),([0,1,2,3,4,168],[]),([0,2,3,4,20,30],[8,131]),([0,1,2,3,20,144],[]),([0,2,4,20,41,101],[]),([0,2,4,20,41,106],[]),([0,1,2,4,20,116],[]),([0,1,2,20,41,163],[15]),([0,1,2,3,4,173],[]),([0,1,2,3,4,146],[]),([0,1,2,3,105,163],[8,128]),([0,1,2,3,4,175],[]),([0,1,2,3,4,101],[]),([0,2,3,4,101,105],[8]),([0,1,3,4,176],[]),([0,1,2,3,4,176],[]),([0,1,3,4,105,176],[8]),([0,1,3,4,105,178],[]),([0,1,2,4,105,179],[8]),([0,1,2,3,4,163],[]),([0,2,3,4,20,101],[8,134]),([0,1,3,4,20,176],[]),([0,2,3,4,22,30],[]),([0,1,3,4,25,153],[7]),([0,1,2,4,25,174],[8]),([0,1,2,3,22,68],[]),([0,1,2,3,4,337],[]),([0,1,2,3,4,327],[15]),([0,1,2,3,4,336],[]),([0,1,2,3,4,332],[]),([0,1,2,3,36,182],[8]),([0,1,2,3,4,231],[]),([0,1,2,3,41,182],[7]),([0,1,2,3,4,232],[]),([0,2,3,4,23,71],[8]),([0,2,3,4,23,30],[15]),([0,1,3,23,25,36],[]),([0,1,2,23,25,41],[]),([0,1,2,3,23,67],[1]),([0,1,2,3,4,47],[]),([0,1,2,3,4,157],[15,140]),([0,1,2,3,4,338],[1,7,8,141]),([0,2,3,23,36,80],[]),([0,2,3,23,36,92],[]),([0,1,3,23,36,155],[8]),([0,1,2,3,36,179],[8]),([0,1,2,3,23,93],[]),([0,1,2,3,4,185],[]),([0,1,3,4,34,155],[]),([0,1,3,4,36,155],[8]),([0,1,2,3,41,155],[7]),([0,1,2,3,43,155],[]),([0,1,2,3,4,177],[]),([0,2,3,4,23,80],[8,142]),([0,1,2,4,23,156],[]),([0,2,3,23,41,101],[]),([0,2,3,23,41,106],[]),([0,1,2,3,23,116],[]),([0,1,2,23,41,179],[7]),([0,1,2,3,4,188],[]),([0,1,2,4,33,179],[]),([0,1,2,3,38,179],[]),([0,1,2,3,4,158],[]),([0,1,2,4,41,179],[7,8]),([0,2,3,4,23,101],[8,143]),([0,1,3,4,23,176],[]),([1,2,3,4,26,27],[]),([0,2,3,4,25,131],[]),([0,2,3,4,25,226],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test5_7 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Block5_7 = true := by decide +kernel
def h7Block5_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,25,276],[145]),([0,2,3,4,25,59],[]),([0,2,3,4,25,204],[]),([0,1,3,4,25,248],[8]),([0,1,2,4,25,250],[8]),([0,1,2,3,25,259],[146]),([1,2,3,4,28,29],[]),([0,1,3,4,25,254],[8]),([0,1,2,4,25,251],[8]),([0,1,2,3,4,75],[7,8,15]),([0,1,3,4,29,36],[15]),([0,1,2,4,29,41],[15]),([0,1,2,3,4,277],[]),([0,1,2,3,4,31],[7,8,15]),([0,1,3,4,30,36],[15]),([0,1,2,4,30,41],[15]),([0,1,2,3,4,46],[]),([0,2,3,4,30,62],[150]),([0,1,3,4,25,139],[8]),([0,1,2,4,25,167],[8]),([0,2,3,4,63,64],[]),([0,1,2,4,25,126],[8,116]),([0,1,2,3,25,144],[129]),([0,1,2,3,25,325],[153]),([0,1,3,4,25,79],[7]),([0,1,3,4,25,80],[7]),([0,1,25,36,41],[7,8,15,17,22]),([0,1,4,25,36,93],[7,8]),([0,1,3,25,36,68],[8,15]),([0,1,2,4,25,100],[8]),([0,1,2,4,25,101],[8]),([0,1,4,25,41,116],[7,8]),([0,1,2,25,41,68],[7,15]),([0,1,2,3,4,283],[]),([0,1,2,3,4,284],[]),([0,1,2,3,4,116],[]),([0,1,3,4,67,116],[8]),([0,1,2,3,4,93],[]),([0,1,2,4,67,93],[8]),([0,1,2,3,4,68],[]),([0,1,2,3,67,68],[8]),([0,1,3,4,25,116],[8]),([0,1,2,4,25,93],[8]),([0,1,2,3,4,206],[]),([0,1,2,3,4,208],[]),([0,1,2,3,4,67],[]),([1,2,3,4,76,77],[]),([0,2,3,4,36,134],[]),([0,2,3,4,36,227],[]),([0,1,2,4,36,286],[159]),([0,2,3,4,36,87],[]),([0,2,3,4,36,212],[]),([0,1,3,4,36,266],[8]),([0,1,2,4,36,272],[160]),([0,1,2,3,36,243],[8]),([1,2,3,4,78,79],[]),([0,1,3,4,36,270],[8]),([0,1,2,3,36,269],[8]),([0,1,2,3,4,96],[7,8,15]),([0,1,2,3,41,79],[7]),([0,1,2,3,4,287],[]),([0,1,2,3,4,81],[7,8,15]),([0,1,2,3,41,80],[7]),([0,1,2,3,4,83],[]),([0,2,3,4,80,90],[164]),([0,1,3,4,36,153],[8]),([0,1,2,3,36,186],[8]),([0,2,3,4,91,92],[]),([0,1,2,4,36,156],[140]),([0,1,2,3,36,128],[8,119])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test5_8 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Block5_8 = true := by decide +kernel
def h7Block5_9 : List NodeSpec := nodesWithIdentity [([0,1,2,4,36,329],[167]),([0,1,2,3,36,100],[8]),([0,1,2,3,36,101],[8]),([0,1,3,36,41,116],[8,15]),([0,1,2,36,41,93],[7,15]),([0,1,3,4,36,116],[8]),([0,1,2,3,36,68],[8]),([0,1,2,3,4,214],[]),([0,1,2,3,4,216],[]),([1,2,3,4,97,98],[]),([0,2,3,4,41,170],[]),([0,2,3,4,41,230],[]),([0,1,3,4,41,285],[]),([0,2,3,4,41,113],[]),([0,2,3,4,41,218],[]),([0,1,3,4,41,293],[]),([0,1,2,4,41,263],[7,8]),([0,1,2,3,41,245],[7,8]),([1,2,3,4,99,100],[]),([0,1,2,4,41,304],[7,8]),([0,1,2,3,41,303],[7,8]),([0,1,2,3,4,119],[7,8,15]),([0,1,2,3,4,294],[]),([0,1,2,3,4,102],[7,8,15]),([0,1,2,3,4,109],[]),([0,2,3,4,101,104],[174]),([0,1,2,4,41,174],[7,8]),([0,1,2,3,41,189],[7,8]),([0,2,3,4,105,106],[]),([0,1,3,4,41,176],[176]),([0,1,2,3,41,163],[7,8,132]),([0,1,3,4,41,328],[]),([0,1,2,4,41,93],[7,8]),([0,1,2,3,41,68],[7,8]),([0,1,2,3,4,220],[]),([0,1,2,3,4,222],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test5_9 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Block5_9 = true := by decide +kernel
def h7Nodes5 : List NodeSpec := h7Block5_0 ++ h7Block5_1 ++ h7Block5_2 ++ h7Block5_3 ++ h7Block5_4 ++ h7Block5_5 ++ h7Block5_6 ++ h7Block5_7 ++ h7Block5_8 ++ h7Block5_9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Check5 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket4 5 h7Nodes5 = true := by
  unfold h7Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h7Test5_0,h7Test5_1⟩,h7Test5_2⟩,h7Test5_3⟩,h7Test5_4⟩,h7Test5_5⟩,h7Test5_6⟩,h7Test5_7⟩,h7Test5_8⟩,h7Test5_9⟩
def h7Bucket5 : BT (List (List Nat)) := buildBucketsBT h7W h7Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G 5 xs.toFinset) h7Bucket5 := buildBucketsBT_sound (by decide) h7Pairs h7WOk h7PoolsOk h7AutosOk h7Bucket4Ok h7Check5
def h7Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,25],[0,1,2,7,8,12]),([0,1,2,3,4,5,36],[0,1,2,8,15,17]),([0,1,3,4,39],[0,2,5,6,20,21]),([0,1,2,3,4,39],[0,2,5,6,7,8,15,20,21]),([0,1,2,3,4,5,41],[0,1,3,7,15,22]),([0,1,2,4,51],[0,3,5,9,16,25]),([0,1,2,3,4,51],[0,3,5,7,8,9,15,16,25]),([0,1,2,3,56],[0,4,5,10,11,26]),([0,1,2,3,4,56],[0,4,5,7,8,10,11,15,26]),([0,2,3,4,6,17],[0,1,5,8,27,30]),([0,2,3,4,6,20],[0,1,5,7,28,31]),([0,2,3,4,6,23],[0,1,5,15,29,32]),([0,1,2,3,4,6,25],[1,7,8,12,27]),([0,1,2,3,4,6,36],[1,8,15,17,27]),([0,1,3,4,136],[1,5,27,39,40,41]),([0,1,2,3,4,136],[0,1,5,7,8,15,27,39,40,41]),([0,1,2,3,4,6,41],[1,7,15,22,28]),([0,1,2,4,125],[1,5,28,36,46,47]),([0,1,2,3,4,125],[0,1,5,7,8,15,28,36,46,47]),([0,1,2,3,127],[1,5,29,33,49,50]),([0,1,2,3,4,127],[0,1,5,7,8,15,29,33,49,50]),([0,1,2,3,4,7,25],[0,1,7,8,51]),([0,1,2,3,4,7,36],[0,1,8,15,51]),([0,1,2,3,4,161],[0,1,7,8,15]),([0,1,2,3,4,7,41],[0,1,7,15,52]),([0,1,2,3,4,181],[0,1,7,8,15]),([0,1,2,3,4,190],[0,1,7,8,15]),([0,2,3,4,8,17],[0,1,5,8,30,54]),([0,2,3,4,8,20],[0,1,5,7,31,55]),([0,2,3,4,8,23],[0,1,5,15,32,56]),([0,1,2,3,4,8,25],[1,5,7,8,54]),([0,1,2,3,4,8,36],[1,5,8,15,54]),([0,1,2,3,4,66],[5,6,7,15,60]),([0,1,2,3,4,8,41],[1,5,7,15,55]),([0,1,2,3,4,70],[5,8,9,15,61]),([0,1,2,3,4,72],[5,7,8,10,62]),([0,1,2,3,4,9,11],[7,8]),([0,1,2,3,4,9,13],[8,15]),([0,1,2,3,4,9,20],[7,8]),([0,1,2,3,4,9,23],[8,15]),([0,1,2,3,4,65],[0,2,5,6,7,8,15,65]),([0,1,2,3,4,9,65],[0,1,5,8,65]),([0,1,2,3,4,9,66],[1,5,60]),([0,1,3,4,9,25],[0,7,8,63,66]),([0,1,3,4,9,36],[0,8,15,64,66]),([0,1,2,3,4,9,41],[7,8,15,63]),([0,1,2,3,4,27],[1,15,71,73]),([0,1,2,3,4,9,27],[5,7,64,73]),([0,1,2,3,4,250],[0,1,7,8,15,63,68,74]),([0,1,2,3,4,9,250],[0,7,8,63]),([0,1,2,3,4,77],[1,7,75,77]),([0,1,2,3,4,9,77],[5,15,63,77]),([0,1,2,3,4,243],[0,1,7,8,15,64,67,78]),([0,1,2,3,4,9,243],[0,8,15,64]),([0,1,2,3,4,10,41],[0,7,8,15,79]),([0,1,2,3,4,251],[0,1,5,7,8,15,81,82]),([0,1,2,3,4,269],[0,1,5,7,8,15,83,84]),([0,1,2,3,4,11,13],[7,15]),([0,1,2,3,4,11,17],[7,8]),([0,1,2,3,4,11,23],[7,15]),([0,1,2,3,4,69],[0,3,5,7,8,9,15,86]),([0,1,2,3,4,11,69],[0,1,5,7,86]),([0,1,2,3,4,11,70],[1,5,61]),([0,1,2,4,11,25],[0,7,8,81,87]),([0,1,2,3,4,11,36],[7,8,15,81]),([0,1,2,3,4,11,27],[5,8,71,85]),([0,1,2,3,4,248],[0,1,7,8,15,72,81,82]),([0,1,2,3,4,11,248],[0,8,81]),([0,1,2,4,11,41],[0,7,15,85,87]),([0,1,2,3,4,98],[1,8,91,92])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test6_0 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket5 6 h7Block6_0 = true := by decide +kernel
def h7Block6_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,11,98],[5,15,81,92]),([0,1,2,3,4,245],[0,1,7,8,15,85,88,94]),([0,1,2,3,4,11,245],[0,7,15,85]),([0,1,2,3,4,12,36],[0,7,8,15,95]),([0,1,2,3,4,254],[0,1,5,7,8,15,63,74]),([0,1,2,3,4,303],[0,1,5,7,8,15,97,98]),([0,1,2,3,4,13,17],[8,15]),([0,1,2,3,4,13,20],[7,15]),([0,1,2,3,4,71],[0,4,5,7,8,10,15,99]),([0,1,2,3,4,13,71],[0,1,5,15,99]),([0,1,2,3,4,13,72],[1,5,62]),([0,1,2,3,4,13,25],[7,8,15,83]),([0,1,2,3,13,36],[0,8,15,83,102]),([0,1,2,3,4,13,77],[5,8,75,97]),([0,1,2,3,4,266],[0,1,7,8,15,76,83,84]),([0,1,2,3,4,13,266],[0,8,83]),([0,1,2,3,13,41],[0,7,15,97,102]),([0,1,2,3,4,13,98],[5,7,83,91]),([0,1,2,3,4,263],[0,1,7,8,15,93,97,98]),([0,1,2,3,4,13,263],[0,7,97]),([0,1,2,3,4,14,25],[0,7,8,15,103]),([0,1,2,3,4,270],[0,1,5,7,8,15,64,78]),([0,1,2,3,4,304],[0,1,5,7,8,15,85,94]),([0,1,2,3,4,16,41],[1,7,8,15,105]),([0,1,2,3,4,167],[0,1,5,7,8,15,107]),([0,1,2,3,4,186],[0,1,5,7,8,15,108]),([0,1,2,3,4,124],[0,1,5,7,8,15,30,57,111]),([0,1,2,3,4,17,124],[0,1,5,8,57]),([0,1,2,3,4,17,66],[0,5,6]),([0,1,2,3,4,17,20],[7,8]),([0,1,2,3,4,17,23],[8,15]),([0,1,3,4,17,25],[1,7,8,30,109]),([0,1,3,4,17,36],[1,8,15,30,110]),([0,1,2,3,4,17,41],[1,7,8,15,109]),([0,1,2,3,4,126],[0,1,7,8,15,109,113,116]),([0,1,2,3,4,17,126],[1,7,8,109]),([0,1,2,3,4,63],[0,15,107,117]),([0,1,2,3,4,17,63],[7,110,117]),([0,1,2,3,4,128],[0,1,7,8,15,110,112,119]),([0,1,2,3,4,17,128],[1,8,15,110]),([0,1,2,3,4,91],[0,7,108,120]),([0,1,2,3,4,17,91],[15,109,120]),([0,1,2,3,4,19,36],[1,7,8,15,122]),([0,1,2,3,4,139],[0,1,5,7,8,15,109,116]),([0,1,2,3,4,189],[0,1,5,7,8,15,124]),([0,1,2,3,4,162],[0,1,5,7,8,15,31,58,127]),([0,1,2,3,4,20,162],[0,1,5,7,58]),([0,1,2,3,4,20,70],[0,5,9]),([0,1,2,3,4,20,23],[7,15]),([0,1,2,4,20,25],[1,7,8,31,125]),([0,1,2,3,4,20,36],[1,7,8,15,125]),([0,1,2,3,4,143],[0,1,7,8,15,107]),([0,1,2,3,4,20,143],[1,8,107,125]),([0,1,2,3,4,20,63],[8,107,126]),([0,1,2,4,20,41],[1,7,15,31,126]),([0,1,2,3,4,163],[0,1,7,8,15,126,128,132]),([0,1,2,3,4,20,163],[1,7,15,126]),([0,1,2,3,4,105],[0,8,124,133]),([0,1,2,3,4,20,105],[15,125,133]),([0,1,2,3,4,22,25],[1,7,8,15,135]),([0,1,2,3,4,153],[0,1,5,7,8,15,110,119]),([0,1,2,3,4,174],[0,1,5,7,8,15,126,132]),([0,1,2,3,4,182],[0,1,5,7,8,15,32,59,139]),([0,1,2,3,4,23,182],[0,1,5,15,59]),([0,1,2,3,4,23,72],[0,5,10]),([0,1,2,3,4,23,25],[1,7,8,15,137]),([0,1,2,3,23,36],[1,8,15,32,137]),([0,1,2,3,4,155],[0,1,7,8,15,108]),([0,1,2,3,4,23,155],[1,8,108,137]),([0,1,2,3,4,23,91],[8,108,138])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test6_1 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket5 6 h7Block6_1 = true := by decide +kernel
def h7Block6_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,23,41],[1,7,15,32,138]),([0,1,2,3,4,179],[0,1,7,8,15,124]),([0,1,2,3,4,23,179],[1,7,124,138]),([0,1,2,3,4,23,105],[7,124,137]),([0,1,2,3,4,25,26],[0,7,8,12,144]),([0,1,2,3,4,25,27],[0,12,71]),([0,1,2,3,4,25,28],[0,147]),([0,1,2,3,4,29],[1,7,8,15,148,149]),([0,1,2,3,4,25,29],[0,7,8,148]),([0,1,2,3,4,30],[0,7,8,15,118,131]),([0,1,2,3,4,25,30],[1,7,8,118]),([0,1,2,3,4,25,62],[1,151]),([0,1,2,3,4,25,63],[1,12,107]),([0,1,2,3,4,25,64],[1,7,8,12,152]),([0,1,3,4,25,36],[7,8,12,15,17]),([0,1,2,4,25,41],[7,8,12,15,22]),([0,1,2,3,4,67],[0,1,12,154,155]),([0,1,2,3,4,25,67],[12,15,154]),([0,1,2,3,4,68],[0,1,7,8,12,156,157]),([0,1,2,3,4,25,68],[7,8,12,15,156]),([0,1,2,3,4,36,76],[0,8,15,17,158]),([0,1,2,3,4,36,77],[0,17,75]),([0,1,2,3,4,36,78],[0,161]),([0,1,2,3,4,79],[1,7,8,15,162,163]),([0,1,2,3,4,36,79],[0,8,15,162]),([0,1,2,3,4,80],[0,7,8,15,121,142]),([0,1,2,3,4,36,80],[1,8,15,121]),([0,1,2,3,4,36,90],[1,165]),([0,1,2,3,4,36,91],[1,17,108]),([0,1,2,3,4,36,92],[1,8,15,17,166]),([0,1,2,3,36,41],[7,8,15,17,22]),([0,1,2,3,4,36,67],[7,154,155]),([0,1,2,3,4,93],[0,1,7,8,15,17,168,169]),([0,1,2,3,4,36,93],[7,8,15,17,168]),([0,1,2,3,4,41,97],[0,7,15,22,170]),([0,1,2,3,4,41,98],[0,22,91]),([0,1,2,3,4,41,99],[0,171]),([0,1,2,3,4,100],[1,7,8,15,172,173]),([0,1,2,3,4,41,100],[0,7,15,172]),([0,1,2,3,4,101],[0,7,8,15,134,143]),([0,1,2,3,4,41,101],[1,7,15,134]),([0,1,2,3,4,41,104],[1,175]),([0,1,2,3,4,41,105],[1,22,124]),([0,1,2,3,4,41,106],[1,7,15,22,177]),([0,1,2,3,4,41,67],[8,154,155]),([0,1,2,3,4,116],[0,1,7,8,15,22,178,179]),([0,1,2,3,4,41,116],[7,8,15,22,178])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test6_2 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket5 6 h7Block6_2 = true := by decide +kernel
def h7Nodes6 : List NodeSpec := h7Block6_0 ++ h7Block6_1 ++ h7Block6_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Check6 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket5 6 h7Nodes6 = true := by
  unfold h7Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h7Test6_0,h7Test6_1⟩,h7Test6_2⟩
def h7Bucket6 : BT (List (List Nat)) := buildBucketsBT h7W h7Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G 6 xs.toFinset) h7Bucket6 := buildBucketsBT_sound (by decide) h7Pairs h7WOk h7PoolsOk h7AutosOk h7Bucket5Ok h7Check6
def h7Block7_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[0,1,2,3,4,5,7,8,15]),([0,1,2,3,4,6],[0,1,5,7,8,15,27,28,29]),([0,1,2,3,4,7],[0,1,7,8,15,51,52,53]),([0,1,2,3,4,8],[0,1,5,7,8,15,54,55,56]),([0,1,2,3,4,9],[0,1,5,7,8,15,63,64]),([0,1,2,3,4,10],[0,1,5,7,8,15,79,80]),([0,1,2,3,4,11],[0,1,5,7,8,15,81,85]),([0,1,2,3,4,12],[0,1,5,7,8,15,95,96]),([0,1,2,3,4,13],[0,1,5,7,8,15,83,97]),([0,1,2,3,4,14],[0,1,5,7,8,15,103,104]),([0,1,2,3,4,16],[0,1,5,7,8,15,105,106]),([0,1,2,3,4,17],[0,1,5,7,8,15,109,110]),([0,1,2,3,4,19],[0,1,5,7,8,15,122,123]),([0,1,2,3,4,20],[0,1,5,7,8,15,125,126]),([0,1,2,3,4,22],[0,1,5,7,8,15,135,136]),([0,1,2,3,4,23],[0,1,5,7,8,15,137,138]),([0,1,2,3,4,25],[0,1,7,8,12,15]),([0,1,2,3,4,36],[0,1,7,8,15,17]),([0,1,2,3,4,41],[0,1,7,8,15,22])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test7_0 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket6 7 h7Block7_0 = true := by decide +kernel
def h7Nodes7 : List NodeSpec := h7Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Check7 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket6 7 h7Nodes7 = true := h7Test7_0
def h7Bucket7 : BT (List (List Nat)) := buildBucketsBT h7W h7Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G 7 xs.toFinset) h7Bucket7 := buildBucketsBT_sound (by decide) h7Pairs h7WOk h7PoolsOk h7AutosOk h7Bucket6Ok h7Check7
def h7Block8_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[7,8,15])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Test8_0 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket7 8 h7Block8_0 = true := by decide +kernel
def h7Nodes8 : List NodeSpec := h7Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Check8 : checkNodesBT h7W h7G h7Mask h7Pools h7Autos h7Bucket7 8 h7Nodes8 = true := h7Test8_0
def h7Bucket8 : BT (List (List Nat)) := buildBucketsBT h7W h7Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h7G 8 xs.toFinset) h7Bucket8 := buildBucketsBT_sound (by decide) h7Pairs h7WOk h7PoolsOk h7AutosOk h7Bucket7Ok h7Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h7Bucket8Ok (by decide +kernel)
def h14R : List Nat := varsOf 47
def h14G : Nat := 0xeeeaeeeaeaa8eaa8eeeaeeeaeaa8eaa8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 9 := carry_of (swaps := [(4,5)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
namespace Cofactor12168
def G_11 : Nat := 0xffc0fc00ffc0fc00ffc0fc00ffc0fc00
def R_11 : List Nat := varsOf 30
def pos_11 : List Nat := [10,10,12,12,14,22,22,22,24,24,26,28,10,10,10,12,12,12,22,24,24,24]
def neg_11 : List Nat := [8,2,8,4,6,20,18,6,16,8,18,20,6,18,20,6,18,20,8,6,18,20]
def fmask_11 : Nat := fullMask 22
def base_11 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x474f3,0x19b4d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x788fc,0x2ad8b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3bff1f,0x40205),(0xffff0000ffff0000ffff0000ffff0000,0x3c0fe0,0x336d60)]
def steps_11 : List (Nat × Nat × Nat) := [(3,0,2),(2,0,1),(2,0,2),(1,0,2),(1,0,1),(0,0,2),(0,0,1),(0,1,7),(3,0,1),(1,5,3),(1,9,1),(3,5,3),(3,1,7),(3,9,1),(3,10,8)]
def W_11 : BT Decor := buildWiresBT 5 base_11 steps_11
def autosL_11 : List (List (Nat × Nat)) := [[],[(2,4)],[(1,2)],[(1,4),(1,2)],[(1,2),(1,4)],[(1,4)]]
def autos_11 : BT (List (Nat × Nat)) := btOfList 3 autosL_11
def slicesL_11 : List (Option (Nat × Nat)) := []
def slices_11 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_11
def ps_11 : List PoolSpec := []
def P_11 : BT (Option BoundPool) := buildPoolsBT 1 W_11 R_11 slices_11 ps_11
lemma gp_11 : goodPairs G_11 pos_11 neg_11 := goodPairs_of (by decide +kernel)
lemma base_11_ok : ∀ x ∈ base_11, faithful pos_11 neg_11 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_11_ok : btAll (fun x => faithful pos_11 neg_11 x ∧ x.1 < 2^128) W_11 := buildWiresBT_faithful base_11_ok
set_option maxRecDepth 500000 in
lemma autos_11_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_11 = G_11) autos_11 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_11_ok : btAll (fun o => ∀ p, o = some p → Slice R_11 G_11 p.1 p.2) slices_11 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_11 G_11 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_11_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_11 G_11 c) P_11 := buildPoolsBT_sound slices_11_ok
def bk_11_init : BT (List (List Nat)) := BT.empty
lemma bk_11_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 (0 - 1) xs.toFinset) bk_11_init := trivial
def nodes_11_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_0 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_init 0 nodes_11_0 = true := by decide +kernel
def bk_11_0 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_0
set_option maxRecDepth 500000 in
lemma bk_11_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 0 xs.toFinset) bk_11_0 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_init_ok chk_11_0
def nodes_11_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_1 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_0 1 nodes_11_1 = true := by decide +kernel
def bk_11_1 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_1
set_option maxRecDepth 500000 in
lemma bk_11_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 1 xs.toFinset) bk_11_1 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_0_ok chk_11_1
def nodes_11_2 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_2 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_1 2 nodes_11_2 = true := by decide +kernel
def bk_11_2 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_2
set_option maxRecDepth 500000 in
lemma bk_11_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 2 xs.toFinset) bk_11_2 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_1_ok chk_11_2
def nodes_11_3 : List NodeSpec := [([6,4,1,3],[],[]),([0,11,2,3],[],[]),([5,12,2,3],[],[0]),([0,1,2,13],[],[]),([0,14,2,3],[],[]),([0,1,15,2],[],[]),([16,0,2,3],[],[]),([17,0,2,3],[],[]),([10,8,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_3 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_2 3 nodes_11_3 = true := by decide +kernel
def bk_11_3 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_3
set_option maxRecDepth 500000 in
lemma bk_11_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 3 xs.toFinset) bk_11_3 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_2_ok chk_11_3
def nodes_11_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([6,0,1,2,3],[],[0]),([0,1,2,7,3],[],[0,1]),([0,1,8,2,3],[],[0]),([9,0,1,2,3],[],[0,1]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_4 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_3 4 nodes_11_4 = true := by decide +kernel
def bk_11_4 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_4
set_option maxRecDepth 500000 in
lemma bk_11_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 4 xs.toFinset) bk_11_4 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_3_ok chk_11_4
def nodes_11_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_11_5 : checkNodesBT W_11 G_11 fmask_11 P_11 autos_11 bk_11_4 5 nodes_11_5 = true := by decide +kernel
def bk_11_5 : BT (List (List Nat)) := buildBucketsBT W_11 nodes_11_5
set_option maxRecDepth 500000 in
lemma bk_11_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_11 5 xs.toFinset) bk_11_5 :=
  buildBucketsBT_sound (by decide) gp_11 W_11_ok P_11_ok autos_11_ok bk_11_4_ok chk_11_5
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_ok : forestRootCheck R_11 G_11 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 4,22,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_11_in : bucketContainsBT bk_11_5 R_11 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_11 : Lower R_11 G_11 6 := lower_of_forestBT root_11_ok bk_11_5_ok root_11_in

def G_12 : Nat := 0xffffff00ff00f000ffffff00ff00f000
def R_12 : List Nat := varsOf 60
lemma low_12_ok : liftCheck 4 0 R_12 G_12 R_0 G_0 [(VAR 2,12,8)] = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 5 := lift_of low_12_ok low_0

def G_30 : Nat := 0xffffff00ff00cc00ffffff00ff00cc00
def R_30 : List Nat := varsOf 58
lemma low_30_ok : carryOK [(1,2)] R_30 G_30 R_12 G_12 = true := by decide +kernel
lemma low_30 : Lower R_30 G_30 5 := carry_of low_30_ok low_12

def G_37 : Nat := 0xffffff00ffc0fc00ffffff00ffc0fc00
def R_37 : List Nat := varsOf 62
def pos_37 : List Nat := [10,10,12,12,14,22,22,22,24,24,26,28,40,40,42,44,46,48,48,50,50,52,52,54,10,10,10,12,12,12,22,22,24,24,24,40,40,40,48,48,48,48]
def neg_37 : List Nat := [8,2,8,4,6,20,18,6,16,8,18,20,32,8,34,36,38,32,16,34,18,36,20,38,18,20,38,18,20,38,8,38,18,20,38,18,20,38,8,18,20,38]
def fmask_37 : Nat := fullMask 42
def base_37 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xc79944f3,0x2adad9944d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf8e188fc,0x336b6e188b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f3f01ff1f,0x4040002205),(0xffff0000ffff0000ffff0000ffff0000,0x3c7c0fe0fe0,0x19b1b540d60),(0xffffffff00000000ffffffff00000000,0x3f800fff000,0x224a4abd000)]
def steps_37 : List (Nat × Nat × Nat) := [(3,2,3),(2,2,3),(1,2,3),(1,0,3),(0,2,3),(3,0,3),(3,0,2),(1,0,2),(1,5,0),(2,7,4),(0,11,3),(3,0,7),(0,0,7),(3,10,2),(1,9,4),(2,0,9),(1,0,9),(0,2,8),(1,10,1),(3,11,3),(1,6,0),(1,10,2),(3,1,12),(3,2,8),(3,12,3),(2,12,3),(1,11,3),(1,12,3),(2,11,3),(0,12,3),(1,6,5),(2,14,0),(2,25,1),(3,1,7),(1,0,19),(2,1,9),(1,1,9),(2,0,19),(3,1,32),(0,14,0),(1,15,1),(1,22,4),(1,1,22),(2,31,4),(3,1,31),(1,15,4),(1,29,1),(2,32,4),(2,14,1),(1,1,19)]
def W_37 : BT Decor := buildWiresBT 6 base_37 steps_37
def autosL_37 : List (List (Nat × Nat)) := [[],[(1,2)]]
def autos_37 : BT (List (Nat × Nat)) := btOfList 1 autosL_37
def slicesL_37 : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,6),some (subcubeFast 4 0,5),some (subcubeFast 6 0,4),some (subcubeFast 2 0,5)]
def slices_37 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_37
def ps_37 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(0,[(1,2,3),(3,0,7)]),(3,[]),(0,[(1,2,3),(0,0,7)]),(0,[(0,2,3),(2,0,9)]),(0,[(0,2,3),(1,0,9)]),(0,[(2,2,3),(3,2,3)]),(0,[(3,0,3),(1,10,1)]),(0,[(1,0,2),(3,1,12)]),(0,[(3,2,3)]),(0,[(2,2,3)]),(0,[(1,2,3)]),(0,[(1,0,3)]),(0,[(0,2,3)]),(0,[(3,0,3)]),(0,[(3,0,2)]),(0,[(1,0,2)])]
def P_37 : BT (Option BoundPool) := buildPoolsBT 5 W_37 R_37 slices_37 ps_37
lemma gp_37 : goodPairs G_37 pos_37 neg_37 := goodPairs_of (by decide +kernel)
lemma base_37_ok : ∀ x ∈ base_37, faithful pos_37 neg_37 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_37_ok : btAll (fun x => faithful pos_37 neg_37 x ∧ x.1 < 2^128) W_37 := buildWiresBT_faithful base_37_ok
set_option maxRecDepth 500000 in
lemma autos_37_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_37 = G_37) autos_37 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_37_0_ok : sliceDirectCheck 32 0 0 R_37 G_37 R_11 G_11 = true := by decide +kernel
lemma sl_37_0 : Slice R_37 G_37 (subcubeFast 32 0) 6 := slice_fast_direct sl_37_0_ok low_11
lemma sl_37_1_ok : sliceDirectCheck 4 0 0 R_37 G_37 R_30 G_30 = true := by decide +kernel
lemma sl_37_1 : Slice R_37 G_37 (subcubeFast 4 0) 5 := slice_fast_direct sl_37_1_ok low_30
lemma sl_37_2_ok : sliceDirectCheck 6 0 0 R_37 G_37 R_0 G_0 = true := by decide +kernel
lemma sl_37_2 : Slice R_37 G_37 (subcubeFast 6 0) 4 := slice_fast_direct sl_37_2_ok low_0
lemma sl_37_3_ok : sliceDirectCheck 2 0 0 R_37 G_37 R_12 G_12 = true := by decide +kernel
lemma sl_37_3 : Slice R_37 G_37 (subcubeFast 2 0) 5 := slice_fast_direct sl_37_3_ok low_12
set_option maxRecDepth 500000 in
lemma slices_37_ok : btAll (fun o => ∀ p, o = some p → Slice R_37 G_37 p.1 p.2) slices_37 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_37 G_37 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_37_0) (forall_cons (fun _ h => by cases h; exact sl_37_1) (forall_cons (fun _ h => by cases h; exact sl_37_2) (forall_cons (fun _ h => by cases h; exact sl_37_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_37_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_37 G_37 c) P_37 := buildPoolsBT_sound slices_37_ok
def bk_37_init : BT (List (List Nat)) := BT.empty
lemma bk_37_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 (0 - 1) xs.toFinset) bk_37_init := trivial
def nodes_37_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_0 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_init 0 nodes_37_0 = true := by decide +kernel
def bk_37_0 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_0
set_option maxRecDepth 500000 in
lemma bk_37_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 0 xs.toFinset) bk_37_0 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_init_ok chk_37_0
def nodes_37_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_1 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_0 1 nodes_37_1 = true := by decide +kernel
def bk_37_1 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_1
set_option maxRecDepth 500000 in
lemma bk_37_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 1 xs.toFinset) bk_37_1 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_0_ok chk_37_1
def nodes_37_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_2 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_1 2 nodes_37_2 = true := by decide +kernel
def bk_37_2 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_2
set_option maxRecDepth 500000 in
lemma bk_37_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 2 xs.toFinset) bk_37_2 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_1_ok chk_37_2
def nodes_37_3 : List NodeSpec := [([53,36,2,3],[],[]),([2,3,39,54],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_3 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_2 3 nodes_37_3 = true := by decide +kernel
def bk_37_3 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_3
set_option maxRecDepth 500000 in
lemma bk_37_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 3 xs.toFinset) bk_37_3 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_2_ok chk_37_3
def nodes_37_4 : List NodeSpec := [([6,35,0,1,4],[],[]),([0,1,2,3,19],[],[]),([36,14,1,2,3],[],[0]),([14,16,1,2,3],[],[]),([37,0,2,3,4],[],[]),([38,16,2,3,4],[],[]),([38,17,2,3,4],[],[]),([0,1,2,7,19],[],[]),([1,2,3,19,39],[],[0]),([35,0,1,2,4],[],[]),([0,1,3,7,19],[],[]),([5,0,1,2,19],[],[]),([6,0,1,3,19],[],[]),([20,1,2,3,19],[],[]),([40,2,21,3,4],[],[]),([14,17,1,2,3],[],[]),([35,0,1,3,4],[],[]),([2,21,41,3,4],[],[]),([5,1,2,21,4],[],[]),([1,2,21,7,4],[],[]),([14,0,1,2,3],[],[]),([42,1,2,3,19],[],[]),([43,0,2,3,4],[],[]),([5,18,0,1,4],[],[]),([44,14,1,2,3],[],[]),([16,1,2,3,4],[],[]),([0,45,2,3,4],[],[]),([0,1,2,3,46],[],[]),([5,0,23,2,4],[],[]),([10,1,2,31,4],[],[]),([0,2,47,3,4],[],[]),([5,35,0,1,4],[],[]),([11,1,26,3,4],[],[]),([48,0,1,2,3],[],[]),([6,5,0,1,4],[],[]),([49,0,2,3,4],[],[]),([0,1,2,3,50],[],[]),([0,51,2,3,4],[],[]),([1,2,34,8,4],[],[]),([52,0,1,2,3],[],[]),([1,2,21,3,19],[],[]),([1,2,21,3,4],[],[]),([0,23,2,7,4],[],[]),([1,22,12,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_4 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_3 4 nodes_37_4 = true := by decide +kernel
def bk_37_4 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_4
set_option maxRecDepth 500000 in
lemma bk_37_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 4 xs.toFinset) bk_37_4 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_3_ok chk_37_4
def nodes_37_5 : List NodeSpec := [([0,13,1,2,3,4],[],[]),([6,5,0,1,3,4],[],[0]),([6,5,0,1,2,4],[],[0]),([14,0,1,2,3,7],[0],[0,1]),([15,0,1,2,3,4],[1,0],[0]),([11,10,1,2,3,4],[2],[0]),([14,0,1,2,3],[],[0,1]),([6,0,1,2,3,4],[],[0]),([16,1,2,3,4],[3],[]),([0,1,2,3,7,4],[4,1,0],[0,1]),([17,1,2,3,7,4],[2,5],[0]),([0,1,9,3,7,4],[],[0]),([18,0,1,2,3,4],[4],[0]),([0,1,9,2,7,4],[],[0,1]),([0,1,9,2,3,19],[0],[0,1]),([11,1,2,12,3,4],[0,2],[]),([0,1,2,3,19],[],[0,1]),([5,0,1,2,3,4],[],[0]),([6,0,1,9,3,4],[0],[0]),([0,1,2,8,7,4],[4],[]),([20,1,9,2,3,4],[2,6],[0,1]),([16,0,1,2,3,4],[],[]),([0,1,2,21,3,4],[],[]),([1,2,21,3,4],[7],[0]),([6,5,0,1,4],[8],[0]),([0,1,22,2,3,4],[1,4,0],[0]),([0,1,9,2,3,4],[4,1,0],[0,1]),([10,1,2,3,8,4],[2],[]),([5,0,1,2,8,4],[4],[]),([5,10,0,1,2,4],[4],[0]),([16,1,2,3,7,4],[4,3],[1,0]),([0,23,2,3,4],[9],[0]),([5,0,1,9,2,4],[0],[0,1]),([0,24,1,2,3,4],[],[]),([0,25,1,2,3,4],[1],[0]),([10,0,23,2,3,4],[1,2],[]),([0,1,2,26,3,4],[],[0]),([27,0,2,12,3,4],[1],[]),([6,0,1,2,7,4],[0],[0]),([28,0,1,2,3,4],[],[]),([29,0,1,2,3,4],[1],[0]),([27,0,2,3,4],[10],[]),([30,0,1,2,3,4],[],[]),([10,0,1,2,7,4],[4],[0]),([0,1,2,3,31,4],[1,0],[0]),([5,0,1,3,7,4],[0],[0]),([0,1,2,3,32,4],[1,0],[0]),([1,9,2,21,3,4],[4,7],[0]),([1,2,12,3,8,4],[2],[0]),([33,0,1,2,3,4],[],[]),([0,1,2,34,3,4],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_5 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_4 5 nodes_37_5 = true := by decide +kernel
def bk_37_5 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_5
set_option maxRecDepth 500000 in
lemma bk_37_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 5 xs.toFinset) bk_37_5 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_4_ok chk_37_5
def nodes_37_6 : List NodeSpec := [([5,0,1,2,3,4],[4,1,0,11],[0,1]),([6,0,1,2,3,4],[4,1,0,12],[0,1]),([0,1,2,3,7,4],[4,13,1],[0,1]),([0,1,2,3,8,4],[4,2,14],[0]),([0,1,9,2,3,4],[4,15,1],[0,1]),([10,0,1,2,3,4],[4,1,2,0,16],[0]),([11,0,1,2,3,4],[4,1,2,0,17],[0]),([0,1,2,12,3,4],[2,18],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_6 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_5 6 nodes_37_6 = true := by decide +kernel
def bk_37_6 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_6
set_option maxRecDepth 500000 in
lemma bk_37_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 6 xs.toFinset) bk_37_6 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_5_ok chk_37_6
def nodes_37_7 : List NodeSpec := [([0,1,2,3,4],[4,2,0],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_37_7 : checkNodesBT W_37 G_37 fmask_37 P_37 autos_37 bk_37_6 7 nodes_37_7 = true := by decide +kernel
def bk_37_7 : BT (List (List Nat)) := buildBucketsBT W_37 nodes_37_7
set_option maxRecDepth 500000 in
lemma bk_37_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_37 7 xs.toFinset) bk_37_7 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok P_37_ok autos_37_ok bk_37_6_ok chk_37_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_37_ok : forestRootCheck R_37 G_37 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 4,22,6),(VAR 5,40,8)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_37_in : bucketContainsBT bk_37_7 R_37 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_37 : Lower R_37 G_37 8 := lower_of_forestBT root_37_ok bk_37_7_ok root_37_in

end Cofactor12168
def h15R : List Nat := varsOf 55
def h15G : Nat := 0xeeeeeaeaeaeae8e8eeeeeaeaeaeae8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 8 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := Cofactor12168.R_37) (T2 := Cofactor12168.G_37) (by decide +kernel) Cofactor12168.low_37
def h16R : List Nat := varsOf 59
def h16G : Nat := 0xeeeeeeaaeeaaee88eeeeeeaaeeaaee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 8 := carry_of (swaps := [(2,3)]) (roots2 := h15R) (T2 := h15G) (by decide +kernel) h15Bound
def h18R : List Nat := varsOf 13
def h18G : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 4 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h19R : List Nat := varsOf 29
def h19G : Nat := 0xfaaafaa0faaafaa0faaafaa0faaafaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 5 := lift_of (z := 16) (o := 0) (essPairs := [(VAR 4,1,17)]) (by decide +kernel) h18Bound
def h20R : List Nat := varsOf 45
def h20G : Nat := 0xfaaafaaafaa0faa0faaafaaafaa0faa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 5 := carry_of (swaps := [(4,5)]) (roots2 := h19R) (T2 := h19G) (by decide +kernel) h19Bound
def h21R : List Nat := varsOf 53
def h21G : Nat := 0xfafaaaaaaaaaa0a0fafaaaaaaaaaa0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 6 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h22R : List Nat := varsOf 57
def h22G : Nat := 0xffaaaaaaaaaaaa00ffaaaaaaaaaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 6 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(2,3)]) (roots2 := h8R) (T2 := h8G) (by decide +kernel) h8Bound
def h23R : List Nat := varsOf 44
def h23G : Nat := 0xfff0fff0f000f000fff0fff0f000f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 4 := carry_of (swaps := [(4,5)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h24R : List Nat := varsOf 60
def h24G : Nat := 0xfff0f000f000f000fff0f000f000f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,36,52)]) (by decide +kernel) h23Bound
def h25R : List Nat := varsOf 45
def h25G : Nat := 0xfffafffafaaafaaafffafffafaaafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 5 := carry_of (swaps := [(4,5)]) (roots2 := h13R) (T2 := h13G) (by decide +kernel) h13Bound
def h17R : List Nat := varsOf 61
def h17G : Nat := 0xfffafaaafaaafaa0fffafaaafaaafaa0
def h17Pos : List Nat := [9,12,5,5,17,12,9,17,33,52,52,56,25,21,56,41,37,17,52,56,12,12,17,5,28,44,28,44,33,28,25,44,41,9,33,33,49,17,21,33,37,28,28,17,44,44,33,49,12,12,12,12]
def h17Neg : List Nat := [8,8,1,4,20,4,1,1,1,20,36,40,24,20,24,40,36,24,48,48,1,0,16,0,20,36,24,40,36,16,1,32,1,0,32,48,48,48,1,40,1,8,4,0,8,4,0,1,24,36,40,20]
def h17Mask : Nat := fullMask 52
def h17Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc9ff50c3b1dd,0x8141401001c4),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf3740afb5262e,0xa240013012638),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xf3603ef38d863,0x512800c02d803),(0xffff0000ffff0000ffff0000ffff0000,0x8e70654e7e90,0x90038254e7210),(0xffffffff00000000ffffffff00000000,0xf19d9a0dcf00,0x600bc9a0d8c00)]
def h17Steps : List (Nat × Nat × Nat) := [(1,0,1),(2,0,1),(1,0,2),(0,1,2),(1,1,2),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(0,3,5),(2,3,5),(0,3,7),(2,3,7),(0,3,9),(1,3,9),(2,3,9),(3,3,9),(0,4,5),(2,4,5),(0,4,7),(2,4,7),(0,4,9),(1,4,9),(2,4,9),(3,4,9),(0,5,7),(1,5,7),(2,5,9),(2,1,2),(3,1,2),(1,1,3),(3,1,3),(1,1,4),(3,1,4),(3,1,7),(1,2,3),(3,2,3),(1,2,4),(3,2,4),(3,2,5),(3,2,7),(1,2,39),(1,1,44),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,0,9),(3,0,9),(0,3,31),(3,3,31),(0,4,31),(3,4,31),(2,5,45),(1,3,56),(2,3,56),(1,4,56),(2,4,56),(1,0,41),(1,1,41),(1,0,68),(3,0,68),(3,2,68),(3,1,69),(2,5,41),(1,0,43),(1,1,43),(1,0,75),(3,0,75),(3,2,75),(3,1,76),(2,5,43),(1,0,10),(1,1,81),(3,1,81),(1,2,81),(3,2,81),(0,3,81),(0,4,81),(1,1,10),(3,0,88),(1,2,88),(3,2,88),(1,2,10),(3,2,82),(2,5,10),(1,1,14),(1,0,15),(3,1,96),(1,2,96),(3,2,96),(1,1,22),(1,0,23),(3,1,101),(1,2,101),(3,2,101),(3,6,7),(1,2,36),(3,0,106),(3,1,106),(2,7,36),(1,2,38),(3,0,110),(3,1,110),(2,7,38),(3,0,92),(3,1,92),(3,1,84),(2,7,10),(1,2,16),(3,2,67),(1,2,24),(3,2,74),(0,2,95),(1,2,95),(2,2,95),(3,2,95),(0,1,118),(2,1,118),(3,1,118),(1,4,48),(2,4,48),(2,9,48),(1,3,87),(1,8,87),(3,4,49),(0,9,49),(3,9,49),(1,1,136),(1,2,136),(1,1,50),(1,2,139),(3,2,139),(1,2,50),(3,1,142),(2,9,50),(0,2,100),(1,2,100),(2,2,100),(3,2,100),(0,1,120),(2,1,120),(3,1,120),(2,3,52),(2,9,52),(1,8,86),(3,3,53),(0,9,53),(3,9,53),(1,1,157),(1,2,157),(1,1,54),(1,2,160),(3,2,160),(1,2,54),(3,1,163),(2,9,54),(2,31,56),(2,9,10),(2,3,167),(2,4,167),(1,1,12),(1,2,12),(1,9,12),(3,1,172),(3,2,172),(0,3,172),(2,9,12),(1,4,176),(1,1,13),(1,2,13),(1,9,13),(3,1,180),(3,2,180),(0,4,180),(2,9,13),(1,3,184),(3,18,19),(1,4,20),(1,3,169),(1,8,169),(3,26,27),(1,8,168),(0,35,42),(0,37,40)]
def h17W : BT Decor := buildWiresBT 8 h17Base h17Steps
def h17AutoList : List (List (Nat × Nat)) := [[]]
def h17Autos : BT (List (Nat × Nat)) := btOfList 1 h17AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Pairs : goodPairs h17G h17Pos h17Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17BaseOk : ∀ x ∈ h17Base, faithful h17Pos h17Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17WOk : btAll (fun x => faithful h17Pos h17Neg x ∧ x.1 < 2^128) h17W := buildWiresBT_faithful h17BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h17G = h17G) h17Autos := btAll_ofList (autos_of (by decide +kernel))
def h17SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 16,4),some (subcubeFast 1 32,4),some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 16 0,5),some (subcubeFast 32 0,5),some (subcubeFast 48 0,4)]
def h17Slices : BT (Option (Nat × Nat)) := btOfList 4 h17SliceList
def h17Specs : List PoolSpec := [(5,[]),(2,[]),(6,[(1,0,1)]),(0,[(1,0,1),(1,0,2)]),(1,[(1,0,1),(1,0,2)]),(5,[(1,0,2)]),(6,[]),(3,[]),(4,[]),(7,[]),(0,[]),(8,[]),(1,[]),(0,[(1,0,1)]),(1,[(1,0,1)]),(9,[]),(6,[(1,0,1),(0,3,31)]),(6,[(1,0,1),(0,4,31)]),(5,[(3,2,5)]),(6,[(2,0,1)]),(6,[(3,1,7)]),(0,[(1,0,2)]),(1,[(1,0,2)]),(5,[(1,0,2),(0,3,31)]),(5,[(1,0,2),(0,4,31)]),(5,[(0,0,3)]),(6,[(0,0,3)]),(5,[(0,0,3),(1,4,48)]),(0,[(1,4,48)]),(5,[(0,0,3),(2,4,48)]),(5,[(0,3,5),(1,2,95)]),(5,[(0,0,3),(2,9,48)]),(5,[(0,3,5)]),(6,[(0,3,7)]),(6,[(0,0,3),(1,4,48)]),(6,[(0,0,3),(2,4,48)]),(5,[(1,0,3)]),(6,[(1,0,3)]),(7,[(0,4,81)]),(5,[(1,0,3),(3,4,49)]),(5,[(1,0,3),(0,9,49)]),(5,[(1,0,3),(3,9,49)]),(1,[(1,0,3)]),(8,[(3,1,3)]),(8,[(3,2,3)]),(6,[(1,0,41)]),(2,[(0,3,4)]),(2,[(3,4,49)]),(6,[(1,0,3),(3,4,49)]),(7,[(3,4,49)]),(5,[(2,0,3)]),(6,[(2,0,3)]),(5,[(3,0,3)]),(6,[(3,0,3)]),(5,[(0,0,4)]),(6,[(0,0,4)]),(1,[(1,0,10)]),(5,[(0,0,4),(2,3,52)]),(5,[(0,4,5),(1,2,100)]),(5,[(0,0,4),(2,9,52)]),(5,[(0,4,5)]),(6,[(0,4,7)]),(6,[(0,0,4),(2,3,52)]),(5,[(1,0,4)]),(6,[(1,0,4)]),(8,[(0,3,81)]),(5,[(1,0,4),(3,3,53)]),(5,[(1,0,4),(0,9,53)]),(5,[(1,0,4),(3,9,53)]),(0,[(1,0,4)]),(7,[(3,1,4)]),(7,[(3,2,4)]),(6,[(1,0,43)]),(2,[(3,3,53)]),(6,[(1,0,4),(3,3,53)]),(8,[(3,3,53)]),(5,[(2,0,4)]),(6,[(2,0,4)]),(5,[(3,0,4)]),(6,[(3,0,4)]),(5,[(0,0,9)]),(5,[(0,0,9),(1,3,56)]),(5,[(0,0,9),(2,3,56)]),(5,[(0,0,9),(1,4,56)]),(5,[(0,0,9),(2,4,56)]),(5,[(1,0,2),(3,3,31)]),(5,[(1,0,2),(3,4,31)]),(5,[(2,5,9)]),(5,[(3,0,9)]),(6,[(3,0,9)]),(5,[(0,3,4)]),(5,[(0,3,4),(1,3,4)]),(5,[(1,3,4)]),(5,[(2,3,4)]),(5,[(2,3,4),(1,9,12)]),(5,[(2,3,4),(2,9,12)]),(5,[(3,3,4)]),(5,[(3,3,4),(1,9,13)]),(5,[(3,3,4),(2,9,13)]),(5,[(0,3,9)]),(5,[(0,3,9),(1,3,9)]),(5,[(1,3,9)]),(5,[(2,3,9)]),(6,[(1,1,41)]),(5,[(1,2,36)]),(5,[(2,3,9),(1,4,20)]),(5,[(3,3,9)]),(5,[(0,4,9)]),(5,[(0,4,9),(1,4,9)]),(5,[(1,4,9)]),(5,[(2,4,9)]),(6,[(1,1,43)]),(5,[(1,2,38)]),(5,[(3,4,9)]),(6,[(1,1,3)]),(5,[(3,2,3)]),(8,[(1,1,3)]),(6,[(3,1,3)]),(5,[(1,2,3)]),(8,[(1,2,3)]),(6,[(1,1,4)]),(5,[(3,2,4)]),(7,[(1,1,4)]),(6,[(3,1,4)]),(5,[(1,2,4)]),(7,[(1,2,4)]),(6,[(0,3,4)]),(6,[(0,3,4),(1,3,4)]),(6,[(1,3,4)]),(6,[(2,3,4)]),(6,[(2,3,4),(1,1,12)]),(8,[(1,1,12)]),(5,[(2,3,4),(1,2,12)]),(8,[(1,2,12)]),(6,[(3,3,4)]),(6,[(3,3,4),(1,1,13)]),(7,[(1,1,13)]),(5,[(3,3,4),(1,2,13)]),(7,[(1,2,13)])]
def h17Pools : BT (Option BoundPool) := buildPoolsBT 8 h17W h17R h17Slices h17Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Slice9 : Slice h17R h17G (subcubeFast 48 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Slice8 : Slice h17R h17G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Slice7 : Slice h17R h17G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Slice6 : Slice h17R h17G (subcubeFast 8 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Slice5 : Slice h17R h17G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Slice4 : Slice h17R h17G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Slice3 : Slice h17R h17G (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Slice2 : Slice h17R h17G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Slice1 : Slice h17R h17G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Slice0 : Slice h17R h17G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h17R h17G p.1 p.2) h17Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h17R h17G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h17Slice0) (forall_cons (fun _ h => by cases h; exact h17Slice1) (forall_cons (fun _ h => by cases h; exact h17Slice2) (forall_cons (fun _ h => by cases h; exact h17Slice3) (forall_cons (fun _ h => by cases h; exact h17Slice4) (forall_cons (fun _ h => by cases h; exact h17Slice5) (forall_cons (fun _ h => by cases h; exact h17Slice6) (forall_cons (fun _ h => by cases h; exact h17Slice7) (forall_cons (fun _ h => by cases h; exact h17Slice8) (forall_cons (fun _ h => by cases h; exact h17Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h17R h17G c) h17Pools := buildPoolsBT_sound h17SlicesOk
def h17Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h17G (3 - 1) xs.toFinset) h17Empty := trivial
def h17Block3_0 : List NodeSpec := nodesWithIdentity [([3,9,30,87],[]),([0,3,9,133],[]),([3,4,30,136],[]),([4,9,30,132],[]),([4,9,30,86],[]),([0,4,9,154],[]),([3,4,30,157],[]),([3,9,30,183],[]),([3,9,30,177],[]),([3,9,30,169],[]),([0,3,9,189],[]),([4,9,30,188],[]),([4,9,30,175],[]),([4,9,30,185],[]),([4,9,30,168],[]),([0,4,9,191],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Test3_0 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Empty 3 h17Block3_0 = true := by decide +kernel
def h17Nodes3 : List NodeSpec := h17Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Check3 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Empty 3 h17Nodes3 = true := h17Test3_0
def h17Bucket3 : BT (List (List Nat)) := buildBucketsBT h17W h17Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h17G 3 xs.toFinset) h17Bucket3 := buildBucketsBT_sound (by decide) h17Pairs h17WOk h17PoolsOk h17AutosOk h17EmptyOk h17Check3
def h17Block4_0 : List NodeSpec := nodesWithIdentity [([0,2,4,39,58],[]),([0,2,3,39,60],[]),([0,1,4,44,58],[]),([0,1,3,44,60],[]),([0,1,2,58,61],[]),([0,1,2,59,60],[]),([0,1,2,59,61],[]),([0,1,3,4,93],[]),([0,2,3,4,116],[]),([0,3,4,122,123],[30]),([0,3,4,123,126],[30]),([0,3,8,9,87],[]),([2,3,4,30,97],[]),([0,3,4,8,136],[41]),([1,2,3,30,87],[]),([0,1,2,3,133],[]),([0,4,8,9,132],[]),([0,3,4,145,146],[58]),([0,3,4,146,149],[58]),([1,2,4,30,132],[]),([0,4,8,9,86],[]),([2,3,4,30,102],[]),([0,3,4,8,157],[68]),([1,2,4,30,86],[]),([0,1,2,4,154],[]),([1,2,3,4,166],[]),([0,1,2,11,167],[15]),([0,1,2,4,186],[]),([0,1,2,21,187],[15]),([0,3,8,9,183],[]),([0,3,8,9,177],[]),([0,3,8,9,169],[]),([0,1,2,3,190],[]),([0,4,8,9,188],[]),([0,1,2,29,188],[15]),([0,4,8,9,175],[]),([0,4,8,9,185],[]),([0,4,8,9,168],[]),([0,2,10,35,112],[]),([0,1,10,42,71],[]),([0,2,10,37,108],[]),([0,1,10,40,78],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Test4_0 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket3 4 h17Block4_0 = true := by decide +kernel
def h17Nodes4 : List NodeSpec := h17Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Check4 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket3 4 h17Nodes4 = true := h17Test4_0
def h17Bucket4 : BT (List (List Nat)) := buildBucketsBT h17W h17Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h17G 4 xs.toFinset) h17Bucket4 := buildBucketsBT_sound (by decide) h17Pairs h17WOk h17PoolsOk h17AutosOk h17Bucket3Ok h17Check4
def h17Block5_0 : List NodeSpec := nodesWithIdentity [([3,4,5,7,9],[0,1,2,3,4,5,6]),([2,3,4,5,7,39],[1]),([1,3,4,5,7,44],[1]),([0,3,4,5,7,9],[0,1,6]),([0,2,3,4,5,39],[0]),([0,1,3,4,7,44],[0]),([0,1,2,3,4,31],[9,10,11,12]),([1,2,3,4,5,62],[]),([2,3,4,5,9,56],[0]),([2,3,4,5,9,57],[0]),([0,3,4,5,9,44],[0,6]),([0,2,3,4,5,68],[1]),([0,1,3,4,41,44],[10]),([0,1,2,3,4,69],[10]),([0,1,2,3,4,73],[6]),([0,2,3,4,5,75],[1]),([0,1,3,4,43,44],[12]),([0,1,2,3,4,76],[12]),([0,1,2,3,4,80],[6]),([0,1,2,3,4,57],[]),([1,2,3,4,31,57],[0]),([0,1,2,3,4,39],[]),([0,2,3,4,31,39],[0]),([0,1,2,3,4,44],[]),([0,1,3,4,31,44],[0]),([0,1,2,4,31,58],[10,15]),([0,1,2,4,31,59],[9]),([0,1,2,3,31,60],[12,15]),([0,1,2,3,31,61],[11]),([1,2,3,4,5,57],[0]),([0,1,2,4,5,58],[16]),([0,1,2,3,5,60],[17]),([1,2,3,4,5,81],[0,7,8]),([0,2,3,4,5,88],[1,9,11]),([0,1,2,3,4,82],[6,9,10]),([0,1,2,3,4,94],[]),([1,2,3,4,5,96],[0]),([1,2,3,4,5,101],[0]),([1,2,3,4,7,105],[]),([1,3,4,7,9,56],[6]),([1,3,4,7,9,57],[6]),([0,3,4,7,9,39],[0,6]),([0,2,3,4,36,39],[10]),([0,1,3,4,7,106],[1]),([0,1,2,3,4,98],[10]),([0,1,2,3,4,109],[0]),([0,2,3,4,38,39],[12]),([0,1,3,4,7,110],[1]),([0,1,2,3,4,103],[12]),([0,1,2,3,4,113],[0]),([1,2,3,4,7,57],[0]),([0,1,2,4,7,58],[23]),([0,1,2,3,7,60],[24]),([1,2,3,4,7,81],[6,7,8]),([0,1,3,4,7,92],[1,9,11]),([0,1,2,3,4,84],[0,9,10]),([0,1,2,3,4,117],[]),([1,2,3,4,7,67],[0]),([1,2,3,4,7,74],[0]),([0,2,3,4,9,95],[6,9,13]),([0,1,3,4,9,118],[0,9,21]),([0,1,2,3,9,129],[9,27,28]),([0,1,2,3,9,130],[29]),([0,1,2,3,4,123],[9,30]),([0,1,2,3,4,131],[0,6,31]),([0,2,3,4,95,122],[1,8,9,15,32]),([0,2,3,4,95,123],[9,13]),([0,2,3,4,95,124],[]),([0,2,3,4,95,125],[]),([0,2,3,4,34,95],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Test5_0 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket4 5 h17Block5_0 = true := by decide +kernel
def h17Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,125],[1]),([0,1,3,4,118,126],[1,8,9,15,33]),([0,1,3,4,118,123],[9,21,30]),([0,1,3,4,118,127],[]),([0,1,3,4,118,128],[]),([0,1,3,4,33,118],[1]),([0,1,2,3,4,128],[1]),([0,1,2,3,9,87],[10,38]),([0,1,2,3,9,134],[39]),([0,1,2,3,4,135],[1,40]),([0,1,2,3,4,136],[41]),([0,1,2,4,49,106],[15]),([0,1,2,4,36,119],[]),([0,2,3,4,8,97],[10]),([0,2,3,4,34,97],[10]),([0,1,2,4,41,97],[]),([0,1,2,3,4,138],[10]),([0,1,2,4,49,68],[15]),([0,1,3,4,33,119],[10]),([0,1,2,3,4,137],[10]),([0,1,2,3,8,87],[10,11,38,46]),([0,1,2,3,33,87],[10,38]),([0,1,2,3,34,87],[10,38]),([0,2,3,4,9,139],[6]),([0,1,3,4,9,142],[0]),([0,1,2,3,4,140],[10,11,12]),([0,1,2,3,4,144],[]),([0,1,2,3,4,141],[]),([0,1,2,3,4,143],[]),([0,2,3,4,9,100],[6,11,14]),([0,1,3,4,9,120],[0,11,22]),([0,1,2,4,9,132],[11,56]),([0,1,2,4,9,152],[57]),([0,1,2,3,4,146],[11,58]),([0,1,2,3,4,153],[0,6,59]),([0,2,3,4,100,145],[1,7,11,15,60]),([0,2,3,4,100,146],[11,14]),([0,2,3,4,100,147],[]),([0,2,3,4,100,148],[]),([0,2,3,4,34,100],[1]),([0,1,2,3,4,148],[1]),([0,1,3,4,120,149],[1,7,11,15,61]),([0,1,3,4,120,146],[11,22,58]),([0,1,3,4,120,150],[]),([0,1,3,4,120,151],[]),([0,1,3,4,33,120],[1]),([0,1,2,3,4,151],[1]),([0,1,2,4,8,132],[1,10,11,15,56]),([0,1,2,4,33,132],[]),([0,1,2,4,34,132],[]),([0,1,2,4,9,86],[12,65]),([0,1,2,4,9,155],[66]),([0,1,2,3,4,156],[1,67]),([0,1,2,3,4,157],[68]),([0,1,2,3,53,110],[15]),([0,1,2,3,38,121],[]),([0,2,3,4,8,102],[12]),([0,2,3,4,34,102],[12]),([0,1,2,3,43,102],[]),([0,1,2,3,4,159],[12]),([0,1,2,3,53,75],[15]),([0,1,3,4,33,121],[12]),([0,1,2,3,4,158],[12]),([0,1,2,4,8,86],[9,12,46,65]),([0,1,2,4,33,86],[12,65]),([0,1,2,4,34,86],[12,65]),([0,2,3,4,9,160],[6]),([0,1,3,4,9,163],[0]),([0,1,2,3,4,161],[9,10,12]),([0,1,2,3,4,165],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Test5_1 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket4 5 h17Block5_1 = true := by decide +kernel
def h17Block5_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,162],[]),([0,1,2,3,4,164],[]),([1,2,3,4,31,56],[]),([0,1,2,4,9,63],[81]),([0,1,2,4,9,64],[82]),([0,1,2,3,9,65],[83]),([0,1,2,3,9,66],[84]),([0,2,3,4,9,39],[0]),([0,1,3,4,9,44],[0]),([0,1,2,4,9,58],[23]),([0,1,2,4,9,59],[85]),([0,1,2,3,9,60],[24]),([0,1,2,3,9,61],[86]),([1,2,3,4,32,57],[]),([0,2,3,4,9,47],[0]),([0,1,3,4,9,46],[0]),([0,2,3,4,9,88],[6]),([0,1,3,4,9,92],[0]),([0,1,2,9,10,11],[9,10,15,91]),([0,1,2,3,4,90],[]),([0,1,2,3,4,167],[9,10]),([0,1,2,3,4,172],[9,94]),([0,1,2,3,4,176],[10,95]),([0,1,2,3,4,180],[9,97]),([0,1,2,3,4,184],[10,98]),([0,1,2,4,18,19],[100]),([0,2,3,4,9,108],[0]),([0,1,3,4,9,71],[0]),([0,2,3,4,9,68],[0,103]),([0,1,3,4,9,106],[0,104]),([0,1,2,4,20,21],[15]),([0,1,2,3,9,187],[9,105]),([0,1,2,3,9,183],[]),([0,1,2,3,9,177],[]),([0,1,2,3,9,169],[10,15]),([0,1,2,3,26,27],[108]),([0,2,3,4,9,112],[0]),([0,1,3,4,9,78],[0]),([0,2,3,4,9,75],[0,111]),([0,1,3,4,9,110],[0,112]),([0,1,2,4,9,188],[11]),([0,1,2,4,9,175],[]),([0,1,2,3,28,29],[15]),([0,1,2,4,9,185],[]),([0,1,2,4,9,168],[12,15]),([0,2,3,4,35,112],[9]),([0,1,3,4,42,71],[10]),([0,1,2,10,35,42],[10]),([0,1,2,3,4,192],[]),([0,1,2,4,10,71],[12]),([0,1,2,4,35,92],[0]),([0,1,2,3,4,99],[]),([0,1,2,3,4,107],[]),([0,2,3,4,37,108],[10]),([0,1,3,4,40,78],[9]),([0,1,2,10,37,40],[10]),([0,1,2,3,4,193],[]),([0,1,2,3,10,78],[10]),([0,1,2,3,37,92],[0]),([0,1,2,3,4,104],[]),([0,1,2,3,4,111],[]),([0,1,2,4,10,108],[12]),([0,1,2,4,40,88],[6]),([0,1,2,3,4,72],[]),([0,1,2,3,4,70],[]),([0,1,2,3,10,112],[10]),([0,1,2,3,42,88],[6]),([0,1,2,3,4,79],[]),([0,1,2,3,4,77],[]),([0,1,2,3,4,83],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Test5_2 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket4 5 h17Block5_2 = true := by decide +kernel
def h17Block5_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,85],[]),([0,1,2,3,4,89],[]),([0,1,2,3,4,91],[]),([0,1,2,3,4,114],[]),([0,1,2,3,4,115],[]),([0,1,2,3,4,174],[9]),([0,1,2,3,4,173],[9]),([0,1,2,3,4,182],[10]),([0,1,2,3,4,181],[10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Test5_3 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket4 5 h17Block5_3 = true := by decide +kernel
def h17Nodes5 : List NodeSpec := h17Block5_0 ++ h17Block5_1 ++ h17Block5_2 ++ h17Block5_3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Check5 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket4 5 h17Nodes5 = true := by
  unfold h17Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h17Test5_0,h17Test5_1⟩,h17Test5_2⟩,h17Test5_3⟩
def h17Bucket5 : BT (List (List Nat)) := buildBucketsBT h17W h17Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h17G 5 xs.toFinset) h17Bucket5 := buildBucketsBT_sound (by decide) h17Pairs h17WOk h17PoolsOk h17AutosOk h17Bucket4Ok h17Check5
def h17Block6_0 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,7],[0,1,2,5,6,7,8]),([0,1,2,3,4,5,7],[0,1,2,5,6]),([1,2,3,4,5,45],[0,1,2,6,7,8]),([0,2,3,4,5,9],[0,1,2,6,13,14]),([0,1,2,3,4,5,41],[0,6,7,9,10]),([0,1,2,3,4,5,43],[0,6,8,11,12]),([0,1,2,3,4,31],[9,10,11,12]),([0,1,2,3,4,5,31],[2,6,7,8]),([0,1,2,3,4,44],[0,1,2,6,9,10,11,12,18]),([0,1,2,3,4,5,44],[0,1,2,6]),([0,1,2,3,4,5,10],[0,1,7,8,9,10,11,12]),([0,1,2,3,4,5,14],[0,1,7,9,10]),([0,1,2,3,4,5,15],[7,9,10]),([0,1,2,3,4,5,22],[0,1,8,11,12]),([0,1,2,3,4,5,23],[8,11,12]),([1,2,3,4,6,7],[0,1,5,6,7,8,19]),([0,1,2,3,4,46],[0,1,5,6,7,8,9,10,11,12,20]),([0,1,3,4,7,9],[0,1,5,6,21,22]),([0,1,2,3,4,7,36],[0,6,7,9,10]),([0,1,2,3,4,7,38],[0,6,8,11,12]),([0,1,2,3,4,7,31],[0,5,7,8]),([0,1,2,3,4,39],[0,1,5,6,9,10,11,12,20]),([0,1,2,3,4,7,39],[0,1,5,6]),([0,1,2,3,4,7,10],[1,6,7,8,9,10,11,12]),([0,1,2,3,4,7,16],[1,6,7,9,10]),([0,1,2,3,4,7,17],[7,9,10]),([0,1,2,3,4,7,24],[1,6,8,11,12]),([0,1,2,3,4,7,25],[8,11,12]),([0,1,2,3,4,47],[0,1,2,6,7,8,9,10,11,12,18]),([0,1,2,3,4,9,48],[0,1,6,9,10,25]),([0,2,3,4,95],[1,7,8,9,32]),([0,1,2,3,4,95],[0,1,6,7,8,9,11,12,32]),([0,1,3,4,118],[1,7,8,9,33]),([0,1,2,3,4,118],[0,1,6,7,8,9,11,12,33]),([0,1,2,3,129],[1,9,12,27,34]),([0,1,2,3,130],[1,9,11,29,35]),([0,1,2,3,4,9,49],[9,10,36]),([0,1,2,4,36,49],[0,1,9,10,15,36,42,43]),([0,1,2,3,4,97],[0,1,6,7,9,10,11,12]),([0,1,2,4,41,49],[1,6,9,10,15,37,42,44]),([0,1,2,3,4,119],[0,1,6,7,9,10,11,12,45]),([0,1,2,3,87],[7,10,11,15,38,46]),([0,1,2,3,134],[7,10,12,39,47,48,49]),([0,1,2,3,4,9,50],[0,1,6,9,10,50]),([0,1,2,3,4,139],[0,1,6,8,10,11,12,50]),([0,1,2,3,4,142],[0,1,6,8,10,11,12,51]),([0,1,2,3,4,9,51],[7,9,10,52]),([0,1,2,3,4,9,52],[0,1,6,11,12,54]),([0,2,3,4,100],[1,7,11,60]),([0,1,2,3,4,100],[0,1,6,7,9,10,11,60]),([0,1,3,4,120],[1,7,11,61]),([0,1,2,3,4,120],[0,1,6,7,9,10,11,61]),([0,1,2,4,132],[1,10,11]),([0,1,2,4,152],[1,9,11,57,62]),([0,1,2,3,4,9,53],[11,12,63]),([0,1,2,3,38,53],[0,1,11,12,15,63,69,70]),([0,1,2,3,4,102],[0,1,6,8,9,10,11,12]),([0,1,2,3,43,53],[1,6,11,12,15,64,69,71]),([0,1,2,3,4,121],[0,1,6,8,9,10,11,12,72]),([0,1,2,4,86],[8,9,12,15,46,65]),([0,1,2,4,155],[7,10,12,66,73,74,75]),([0,1,2,3,4,9,54],[0,1,6,11,12,76]),([0,1,2,3,4,160],[0,1,6,7,9,10,12,76]),([0,1,2,3,4,163],[0,1,6,7,9,10,12,77]),([0,1,2,3,4,9,55],[8,11,12,78]),([0,1,2,3,4,9,56],[0,1,6,80]),([0,1,2,3,4,9,31],[1,5]),([0,1,2,3,4,9,32],[1,87]),([0,1,2,3,4,57],[0,6,9,10,11,12,88,89]),([0,1,2,3,4,9,57],[0,1,6,88])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Test6_0 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket5 6 h17Block6_0 = true := by decide +kernel
def h17Block6_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,9,10],[0,6,9,10,11,12,90]),([0,1,2,3,4,9,11],[9,10,11,12,15,92]),([0,1,2,3,4,9,12],[9,10,11,12,93]),([0,1,2,3,4,9,13],[9,10,11,12,96]),([0,1,2,3,4,9,18],[9,10,99]),([0,1,2,3,4,9,19],[9,10,101]),([0,1,2,3,4,9,20],[9,10,102]),([0,1,2,3,4,9,21],[9,10,106]),([0,1,2,3,4,9,26],[11,12,107]),([0,1,2,3,4,9,27],[11,12,109]),([0,1,2,3,4,9,28],[11,12,110]),([0,1,2,3,4,9,29],[11,12,113]),([0,1,2,4,35,41],[0,6,7,9,10,44,114,115,116]),([0,1,2,3,4,35,42],[0,6,9,10,11,12]),([0,1,2,3,4,71],[0,1,6,7,9,10,11,12,103,115]),([0,1,2,4,10,35],[0,7,9,10,12,46,90,116]),([0,1,2,3,4,96],[0,1,6,7,9,10,11,12]),([0,1,2,4,36,40],[0,6,7,9,10,43,117,118,119]),([0,1,2,3,4,106],[0,1,6,9,10,11,12,15,104,117]),([0,1,2,3,4,37,40],[0,6,9,10,11,12]),([0,1,2,3,37,43],[0,6,8,11,12,71,120,121,122]),([0,1,2,3,4,78],[0,1,6,8,9,10,11,12,111,121]),([0,1,2,3,10,37],[0,8,10,11,12,46,90,122]),([0,1,2,3,4,101],[0,1,6,8,9,10,11,12]),([0,1,2,3,38,42],[0,6,8,11,12,70,123,124,125]),([0,1,2,3,4,110],[0,1,6,9,10,11,12,15,112,123]),([0,1,2,3,4,108],[0,1,6,7,9,10,11,12,104,117]),([0,1,2,4,10,40],[6,7,9,10,12,46,119,126]),([0,1,2,3,4,67],[0,1,6,7,9,10,11,12,45]),([0,1,2,3,4,68],[0,1,6,9,10,11,12,15,103,115]),([0,1,2,3,4,112],[0,1,6,8,9,10,11,12,112,123]),([0,1,2,3,10,42],[6,8,10,11,12,46,125,126]),([0,1,2,3,4,74],[0,1,6,8,9,10,11,12,72]),([0,1,2,3,4,75],[0,1,6,9,10,11,12,15,111,121]),([0,1,2,3,4,81],[0,1,6,7,8,9,10,11,46]),([0,1,2,3,4,88],[0,1,6,9,10,11,90]),([0,1,2,3,4,92],[0,1,6,9,10,11,126]),([0,1,2,10,11],[7,9,10,15,46,91,127]),([0,1,2,3,4,170],[0,1,6,8,9,10,12,15,93,130,131]),([0,1,2,3,4,171],[0,1,6,8,9,10,12,15,129,132,133]),([0,1,2,3,4,178],[0,1,6,7,9,10,11,15,96,135,136]),([0,1,2,3,4,179],[0,1,6,7,9,10,11,15,134,137,138])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Test6_1 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket5 6 h17Block6_1 = true := by decide +kernel
def h17Nodes6 : List NodeSpec := h17Block6_0 ++ h17Block6_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Check6 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket5 6 h17Nodes6 = true := by
  unfold h17Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h17Test6_0,h17Test6_1⟩
def h17Bucket6 : BT (List (List Nat)) := buildBucketsBT h17W h17Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h17G 6 xs.toFinset) h17Bucket6 := buildBucketsBT_sound (by decide) h17Pairs h17WOk h17PoolsOk h17AutosOk h17Bucket5Ok h17Check6
def h17Block7_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[0,1,2,6,7,8,9,10,11,12]),([0,1,2,3,4,6],[0,1,6,7,8,9,10,11,12,19]),([0,1,2,3,4,7],[0,1,5,6,7,8,9,10,11,12]),([0,1,2,3,4,45],[0,1,6,7,8,9,10,11,12]),([0,1,2,3,4,48],[0,1,6,7,8,9,11,12,25,26]),([0,1,2,3,4,49],[0,1,6,7,8,9,10,11,12,15,36,37]),([0,1,2,3,4,50],[0,1,6,8,9,10,11,12,50,51]),([0,1,2,3,4,51],[0,1,6,7,8,9,10,11,12,15,52,53]),([0,1,2,3,4,52],[0,1,6,7,9,10,11,54,55]),([0,1,2,3,4,53],[0,1,6,7,8,9,10,11,12,15,63,64]),([0,1,2,3,4,54],[0,1,6,7,9,10,11,12,76,77]),([0,1,2,3,4,55],[0,1,6,7,8,9,10,11,12,15,78,79]),([0,1,2,3,4,9],[0,1,6,9,10,11,12]),([0,1,2,3,4,35],[0,1,6,7,9,10,11,12,15,114]),([0,1,2,3,4,36],[0,1,6,7,9,11,12,15,117]),([0,1,2,3,4,37],[0,1,6,8,9,10,11,12,15,120]),([0,1,2,3,4,38],[0,1,6,8,9,10,11,15,123]),([0,1,2,3,4,40],[0,1,6,7,9,10,11,12,15,118]),([0,1,2,3,4,41],[0,1,6,7,9,11,12,15,115]),([0,1,2,3,4,42],[0,1,6,8,9,10,11,12,15,124]),([0,1,2,3,4,43],[0,1,6,8,9,10,11,15,121]),([0,1,2,3,4,10],[0,1,6,7,8,9,10,11,90,126]),([0,1,2,3,4,11],[0,1,6,7,9,10,11,12,15,92,128]),([0,1,2,3,4,12],[0,1,6,7,8,9,10,11,12,15,93,129]),([0,1,2,3,4,13],[0,1,6,7,9,10,11,15,96,134])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Test7_0 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket6 7 h17Block7_0 = true := by decide +kernel
def h17Nodes7 : List NodeSpec := h17Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Check7 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket6 7 h17Nodes7 = true := h17Test7_0
def h17Bucket7 : BT (List (List Nat)) := buildBucketsBT h17W h17Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h17G 7 xs.toFinset) h17Bucket7 := buildBucketsBT_sound (by decide) h17Pairs h17WOk h17PoolsOk h17AutosOk h17Bucket6Ok h17Check7
def h17Block8_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Test8_0 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket7 8 h17Block8_0 = true := by decide +kernel
def h17Nodes8 : List NodeSpec := h17Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Check8 : checkNodesBT h17W h17G h17Mask h17Pools h17Autos h17Bucket7 8 h17Nodes8 = true := h17Test8_0
def h17Bucket8 : BT (List (List Nat)) := buildBucketsBT h17W h17Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h17G 8 xs.toFinset) h17Bucket8 := buildBucketsBT_sound (by decide) h17Pairs h17WOk h17PoolsOk h17AutosOk h17Bucket7Ok h17Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 9 := lower_of_forestBT (essPairs := [(VAR 0,4,5),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h17Bucket8Ok (by decide +kernel)
def h27R : List Nat := varsOf 14
def h27G : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 4 := carry_of (swaps := [(1,2),(2,3),(3,4)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h28R : List Nat := varsOf 22
def h28G : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 4 := carry_of (swaps := [(1,2),(2,3)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h29R : List Nat := varsOf 26
def h29G : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 4 := carry_of (swaps := [(1,2)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h30R : List Nat := varsOf 30
def h30G : Nat := 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 7 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h31R : List Nat := varsOf 38
def h31G : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 4 := carry_of (swaps := [(4,5),(1,2),(2,3)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h32R : List Nat := varsOf 42
def h32G : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 4 := carry_of (swaps := [(4,5),(1,2)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h33R : List Nat := varsOf 46
def h33G : Nat := 0xfffcfffcfcc0fcc0fffcfffcfcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 7 := carry_of (swaps := [(1,2),(2,3),(3,4)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h34R : List Nat := varsOf 50
def h34G : Nat := 0xffffcccccccc0000ffffcccccccc0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 4 := carry_of (swaps := [(4,5),(3,4),(1,2)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h35R : List Nat := varsOf 52
def h35G : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 4 := carry_of (swaps := [(4,5),(3,4)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h36R : List Nat := varsOf 54
def h36G : Nat := 0xfffffcfcfcfcc0c0fffffcfcfcfcc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 7 := carry_of (swaps := [(1,2),(2,3)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h37R : List Nat := varsOf 56
def h37G : Nat := 0xffffff00ff000000ffffff00ff000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 4 := carry_of (swaps := [(4,5),(3,4),(2,3)]) (roots2 := h11R) (T2 := h11G) (by decide +kernel) h11Bound
def h38R : List Nat := varsOf 58
def h38G : Nat := 0xffffffccffcccc00ffffffccffcccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 7 := carry_of (swaps := [(1,2)]) (roots2 := h5R) (T2 := h5G) (by decide +kernel) h5Bound
def h26R : List Nat := varsOf 62
def h26G : Nat := 0xfffffffcfffcfcc0fffffffcfffcfcc0
def h26Pos : List Nat := [10,12,6,6,12,10,18,34,48,48,20,18,24,20,34,36,40,36,24,40,10,20,50,44,28,36,6,24,44,28,40,12,18,52,42,6,10,12,52,56,28,48,26,34,6,10,12,52,56,24,42,26,40,50,26,48,50,14,6,10,12,48,48,22,18,34,20,36,18,34,14,34,18,14,36,40,20,24,20,36]
def h26Neg : List Nat := [8,8,2,4,4,2,2,2,16,32,4,16,8,16,32,4,8,32,16,32,4,2,2,4,4,2,8,2,8,8,2,2,4,4,2,16,16,16,16,16,16,2,2,4,32,32,32,32,32,4,8,8,4,16,16,4,32,8,0,0,0,8,0,16,8,8,8,8,0,0,2,16,32,4,16,16,32,32,0,0]
def h26Mask : Nat := fullMask 80
def h26Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x3f38f6c3c1d045048ed,0x4000000604ca6000e4),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xd64c9600d16ab7a2a41e,0x2000092080301908418),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x2a401a5f65b4f99d1033,0xf220c000034011003),(0xffff0000ffff0000ffff0000ffff0000,0x7115e1eb87c329643f40,0xc80806001f800042900),(0xffffffff00000000ffffffff00000000,0x8caa61b58ac652cbc380,0x31000101f000000a4200)]
def h26Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(0,1,2),(1,1,2),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(1,3,6),(1,4,10),(1,12,14),(2,12,14),(3,12,14),(1,12,17),(3,12,17),(1,12,18),(3,12,18),(1,14,17),(3,14,17),(1,14,18),(3,14,18),(1,17,18),(2,4,10),(3,4,10),(1,4,12),(3,10,14),(3,10,17),(3,10,33),(2,4,12),(3,4,12),(3,4,17),(0,10,12),(1,10,12),(2,3,6),(3,3,6),(1,3,10),(1,4,6),(2,4,6),(3,4,6),(3,6,14),(3,6,33),(3,6,44),(3,4,44),(0,6,12),(2,3,10),(3,3,10),(1,3,12),(3,4,55),(0,6,10),(2,3,12),(3,3,12),(3,3,45),(3,3,18),(3,3,33),(3,10,26),(0,12,26),(3,12,26),(3,6,28),(0,12,28),(0,6,19),(0,10,19),(1,3,32),(1,3,38),(1,3,39),(1,10,39),(1,12,39),(1,4,43),(1,6,51),(1,4,54),(1,4,59),(1,10,60),(1,12,60),(1,6,61),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(0,2,3),(1,2,3),(1,4,85),(3,4,85),(1,4,87),(2,10,85),(2,45,85),(3,85,90),(3,4,87),(0,10,87),(2,45,87),(0,85,87),(2,47,85),(1,47,94),(1,47,87),(2,6,87),(2,18,87),(3,87,88),(0,6,85),(2,6,85),(2,18,85),(1,32,85),(2,2,3),(3,2,3),(0,2,4),(1,2,4),(2,6,111),(0,10,111),(0,14,85),(3,14,85),(0,14,111),(3,14,111),(2,85,111),(2,44,111),(3,4,111),(3,3,85),(3,3,111),(3,3,88),(3,2,4),(3,2,6),(3,2,10),(3,2,55),(1,4,127),(3,6,127),(3,2,14),(3,2,45),(3,2,18),(3,2,28),(3,2,44),(1,2,47),(1,2,51),(3,2,88),(1,2,89),(1,2,54),(1,2,32),(1,3,89),(1,6,138),(3,1,3),(0,1,4),(1,1,4),(0,6,145),(2,6,145),(2,10,145),(0,14,87),(0,14,145),(2,87,145),(2,17,145),(3,4,145),(2,17,111),(0,111,145),(1,43,122),(1,43,111),(2,44,145),(1,54,145),(3,2,33),(1,3,160),(1,4,160),(3,6,160),(3,2,17),(1,2,43),(1,2,123),(1,4,123),(1,6,166),(1,2,61),(3,1,4),(3,1,10),(3,1,55),(1,4,172),(3,1,14),(3,1,45),(3,1,18),(3,1,26),(3,1,17),(1,1,32),(1,1,39),(3,1,90),(1,1,94),(1,1,43),(1,1,47),(1,3,94),(3,1,33),(1,3,186),(1,4,186),(3,1,44),(1,1,122),(1,4,122),(1,1,54),(1,1,60),(0,2,26),(3,2,26),(0,1,28),(3,1,28),(1,1,164),(1,3,164),(1,4,164),(1,2,39),(3,2,75),(1,2,189),(1,3,189),(1,4,189),(1,1,51),(3,1,77),(1,1,131),(1,3,131),(1,4,131),(1,2,60),(3,2,72),(1,2,176),(1,3,176),(1,4,176),(1,1,61),(3,1,70),(3,0,2),(0,0,3),(1,0,3),(2,12,220),(2,45,220),(2,90,220),(1,4,220),(3,4,220),(0,12,87),(0,87,220),(2,87,220),(2,47,220),(2,94,220),(0,6,220),(2,6,220),(2,33,220),(1,38,220),(0,12,111),(0,14,220),(3,14,220),(3,3,220),(3,3,224),(1,4,134),(0,19,220),(0,2,224),(1,2,59),(1,2,38),(1,3,225),(0,4,41),(3,4,41),(0,85,220),(1,85,131),(1,131,220),(1,6,137),(0,87,111),(0,3,41),(3,3,41),(3,14,41),(1,14,125),(1,134,145),(1,3,133),(1,2,172),(0,1,224),(1,1,125),(2,87,125),(1,2,94),(0,14,24),(0,3,24),(1,1,15),(3,15,41),(2,4,253),(1,4,254),(1,3,247),(1,1,130),(1,4,130),(3,3,210),(1,134,153),(3,1,240),(1,2,174),(1,4,174),(3,3,135),(1,2,177),(1,3,177),(1,4,177),(1,1,133),(3,1,136),(3,0,3),(0,0,4),(1,0,4),(0,6,286),(2,6,286),(2,12,286),(0,14,286),(2,87,286),(2,17,286),(3,4,286),(0,111,286),(2,111,286),(2,55,286),(1,59,286),(1,4,132),(0,19,286),(1,4,239),(1,127,286),(0,145,286),(0,14,22),(0,4,22),(1,2,186),(2,111,125),(1,2,122),(1,1,16),(3,16,41),(2,3,246),(1,3,130),(3,4,199),(1,121,132),(3,1,258),(1,3,174),(3,4,165),(1,82,239),(3,1,169),(3,0,4),(3,0,12),(3,0,44),(1,4,321),(3,0,14),(3,0,45),(0,0,33),(3,0,33),(3,0,26),(3,0,17),(1,0,38),(1,0,39),(0,0,90),(3,0,90),(1,0,94),(1,0,43),(1,0,47),(3,0,18),(1,3,336),(1,4,336),(0,0,55),(3,0,55),(1,0,122),(1,0,59),(1,0,60),(0,0,19),(3,0,19),(1,0,164),(1,2,340),(1,3,340),(1,4,340),(1,0,56),(3,0,78),(1,0,131),(1,2,326),(1,3,326),(1,4,326),(1,0,62),(3,0,71),(1,2,321),(0,0,88),(1,0,125),(1,0,15),(1,0,130),(1,127,293),(3,0,128),(1,2,323),(1,4,323),(1,2,327),(1,3,327),(1,4,327),(1,0,137),(3,0,138),(1,2,336),(1,0,16),(1,160,238),(3,0,161),(1,3,323),(1,123,126),(3,0,166),(1,0,189),(1,1,321),(1,4,380),(3,4,380),(1,4,379),(3,4,379),(1,0,42),(1,1,42),(1,1,345),(1,0,197),(3,1,333),(3,0,182),(2,22,293),(3,15,22),(3,5,99),(1,0,86),(1,1,86),(3,86,99),(1,0,176),(1,1,336),(1,3,398),(3,3,398),(1,3,397),(3,3,397),(1,0,46),(1,1,46),(3,1,341),(3,0,190),(2,24,238),(3,16,24),(3,5,156),(1,0,110),(1,1,110),(3,110,156),(1,0,13),(1,41,413),(1,1,13),(3,13,41),(2,22,253),(1,0,129),(1,1,129),(2,24,246),(1,0,163),(1,1,163),(1,0,177),(1,1,323),(1,2,424),(3,2,424),(1,2,423),(3,2,423),(3,1,362),(3,0,271),(2,26,126),(2,26,82),(2,26,40),(3,5,26),(1,1,59),(1,1,38),(1,1,127),(1,14,171),(3,3,215),(1,111,178),(1,120,178),(3,2,281),(1,87,176),(3,3,179),(3,2,180),(1,1,160),(3,4,204),(1,108,175),(3,2,280),(3,4,192),(1,83,239),(3,2,193),(1,0,54),(1,0,32),(1,4,347),(3,4,347),(1,0,53),(1,0,171),(3,4,346),(3,2,330),(3,9,99),(3,84,99),(1,3,353),(3,3,353),(1,0,31),(3,3,352),(1,9,123),(3,2,343),(3,9,156),(3,144,156),(1,172,293),(3,0,173),(1,186,238),(3,0,187),(3,1,365),(3,0,276),(3,7,28),(2,28,83),(2,28,52),(3,9,28),(1,124,178),(3,4,203),(1,109,175),(3,3,213),(1,134,170),(3,4,198),(1,132,143),(3,3,208),(1,1,320),(1,4,348),(3,4,348),(3,4,342),(3,3,329),(3,11,99),(2,99,219),(2,22,219),(3,2,368),(1,160,219),(1,134,144),(1,110,178),(3,1,337),(1,186,219),(2,26,260),(2,28,242),(3,104,177),(3,95,133),(3,3,355),(1,11,239),(3,11,156),(2,156,285),(2,24,285),(3,2,369),(1,127,285),(1,84,132),(1,86,175),(3,1,322),(1,172,285),(3,146,177),(3,113,133),(1,120,328),(1,108,324),(1,123,218),(1,153,321),(1,121,336),(2,22,339),(2,24,325),(1,124,328),(1,110,328),(1,109,324),(1,127,319),(1,160,284),(1,84,336),(2,26,359),(3,231,327),(1,86,324),(1,144,321),(3,287,327),(1,170,321),(1,172,319),(1,143,336),(1,186,284),(2,28,331),(2,177,415),(2,133,252),(2,327,413)]
def h26W : BT Decor := buildWiresBT 10 h26Base h26Steps
def h26AutoList : List (List (Nat × Nat)) := [[]]
def h26Autos : BT (List (Nat × Nat)) := btOfList 1 h26AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Pairs : goodPairs h26G h26Pos h26Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26BaseOk : ∀ x ∈ h26Base, faithful h26Pos h26Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26WOk : btAll (fun x => faithful h26Pos h26Neg x ∧ x.1 < 2^128) h26W := buildWiresBT_faithful h26BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h26G = h26G) h26Autos := btAll_ofList (autos_of (by decide +kernel))
def h26SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,7),some (subcubeFast 4 0,7),some (subcubeFast 6 0,4),some (subcubeFast 8 0,7),some (subcubeFast 10 0,4),some (subcubeFast 12 0,4),some (subcubeFast 16 0,7),some (subcubeFast 18 0,4),some (subcubeFast 20 0,4),some (subcubeFast 24 0,4),some (subcubeFast 32 0,7),some (subcubeFast 34 0,4),some (subcubeFast 36 0,4),some (subcubeFast 40 0,4),some (subcubeFast 48 0,4)]
def h26Slices : BT (Option (Nat × Nat)) := btOfList 4 h26SliceList
def h26Specs : List PoolSpec := [(0,[]),(1,[]),(1,[(1,0,2)]),(6,[(1,0,1),(1,0,2),(1,1,2)]),(8,[]),(7,[]),(12,[]),(11,[]),(1,[(1,3,4)]),(0,[(1,3,4)]),(3,[]),(2,[]),(4,[]),(5,[]),(10,[(1,0,1),(1,0,2),(1,1,2)]),(6,[(1,0,2),(1,1,2),(1,0,1)]),(3,[(1,0,1),(1,3,6)]),(1,[(1,3,6)]),(0,[(1,3,6)]),(3,[(1,0,1)]),(6,[(1,0,1),(1,1,2),(1,0,2)]),(1,[(1,0,2),(1,3,10)]),(9,[]),(0,[(1,3,10)]),(0,[(1,1,2),(1,3,12)]),(1,[(1,3,12)]),(0,[(1,1,2)]),(10,[(1,0,2),(1,1,2),(1,0,1)]),(3,[(1,0,1),(1,4,6)]),(1,[(1,4,6)]),(0,[(1,4,6)]),(10,[(1,0,1),(1,1,2),(1,0,2)]),(1,[(1,0,2),(1,4,10)]),(13,[]),(0,[(1,4,10)]),(0,[(1,1,2),(1,4,12)]),(1,[(1,4,12)]),(3,[(1,0,1),(1,1,3)]),(6,[(1,0,1),(1,0,2)]),(0,[(1,1,3)]),(3,[(1,0,1),(1,3,10),(1,1,3)]),(3,[(1,0,1),(1,1,4)]),(10,[(1,0,1),(1,0,2)]),(0,[(1,1,4)]),(3,[(1,0,1),(1,4,10),(1,1,4)]),(1,[(1,0,2),(1,2,3)]),(0,[(1,2,3)]),(1,[(1,0,2),(1,3,6),(1,2,3)]),(1,[(1,0,2),(1,2,4)]),(0,[(1,2,4)]),(1,[(1,0,2),(1,4,6),(1,2,4)]),(3,[(1,3,4)]),(1,[(1,0,2),(1,3,6)]),(6,[(1,0,2),(1,0,1)]),(3,[(1,0,1),(1,3,6),(3,4,17)]),(1,[(1,0,2),(3,3,6)]),(3,[(1,0,1),(3,3,6)]),(0,[(3,3,6)]),(3,[(1,0,1),(1,3,10)]),(1,[(1,0,2),(1,3,10),(3,4,44)]),(3,[(1,3,10)]),(1,[(1,0,2),(3,3,10)]),(3,[(1,0,1),(3,3,10)]),(0,[(3,3,10)]),(1,[(1,0,2),(1,4,6)]),(10,[(1,0,2),(1,0,1)]),(3,[(1,0,1),(1,4,6),(3,3,45)]),(1,[(1,0,2),(3,4,6)]),(3,[(1,0,1),(3,4,6)]),(0,[(3,4,6)]),(3,[(1,0,1),(1,4,10)]),(1,[(1,0,2),(1,4,10),(3,3,18)]),(3,[(1,4,10)]),(1,[(1,0,2),(3,4,10)]),(3,[(1,0,1),(3,4,10)]),(0,[(3,4,10)]),(1,[(1,0,3)]),(3,[(1,0,1),(1,0,3)]),(6,[(1,0,1),(1,1,2)]),(3,[(1,0,1),(1,3,12),(1,0,3)]),(3,[(1,0,1),(1,1,3),(1,0,3)]),(6,[]),(1,[(1,2,4)]),(10,[(1,0,1),(1,1,3),(1,0,3)]),(3,[(1,10,12),(1,1,3),(1,0,3)]),(6,[(1,0,1)]),(6,[(1,0,1),(1,4,6)]),(0,[(1,1,3),(1,4,85)]),(14,[]),(1,[(1,4,85)]),(1,[(1,0,3),(1,4,220)]),(0,[(1,4,220)]),(6,[(1,0,1),(1,1,4)]),(10,[(1,0,1),(1,0,3)]),(6,[(1,0,1),(1,1,4),(1,4,220)]),(1,[(1,2,3),(1,0,3)]),(1,[(1,0,2),(1,2,3),(1,0,3)]),(6,[(1,2,4)]),(1,[(1,0,2),(1,0,3)]),(3,[(1,10,12),(1,0,3)]),(1,[(3,2,6),(1,0,3)]),(6,[(1,0,1),(3,2,6)]),(0,[(3,2,6)]),(6,[(1,0,2)]),(0,[(1,3,10),(3,2,44)]),(1,[(1,3,4),(1,0,3)]),(1,[(1,3,4),(1,4,6),(1,0,3)]),(1,[(1,4,6),(1,0,3)]),(6,[(1,0,1),(1,4,6),(3,2,45)]),(1,[(3,4,6),(1,0,3)]),(6,[(1,0,1),(3,4,6)]),(6,[(1,0,1),(1,4,220)]),(6,[(1,4,220)]),(1,[(1,0,3),(3,4,220)]),(6,[(1,0,1),(3,4,220)]),(0,[(3,4,220)]),(1,[(1,0,4)]),(3,[(1,0,1),(1,0,4)]),(10,[(1,0,1),(1,1,2)]),(3,[(1,0,1),(1,4,12),(1,0,4)]),(6,[(1,0,1),(1,0,4)]),(10,[(1,0,1),(1,1,3)]),(6,[(1,0,1),(1,4,85),(1,0,4)]),(3,[(1,0,1),(1,1,4),(1,0,4)]),(10,[]),(1,[(1,2,3)]),(6,[(1,0,1),(1,1,4),(1,0,4)]),(3,[(1,10,12),(1,1,4),(1,0,4)]),(10,[(1,0,1)]),(10,[(1,0,1),(1,3,6)]),(10,[(1,2,3)]),(1,[(1,2,4),(1,0,4)]),(1,[(1,0,2),(1,2,4),(1,0,4)]),(1,[(1,0,2),(1,0,4)]),(3,[(1,10,12),(1,0,4)]),(1,[(3,2,6),(1,0,4)]),(10,[(1,0,1),(3,2,6)]),(10,[(1,0,2)]),(0,[(1,4,10),(3,2,18)]),(1,[(1,3,4),(1,0,4)]),(1,[(1,3,4),(1,3,6),(1,0,4)]),(1,[(1,3,6),(1,0,4)]),(10,[(1,0,1),(1,3,6),(3,2,17)]),(1,[(3,3,6),(1,0,4)]),(10,[(1,0,1),(3,3,6)]),(10,[(1,0,3)]),(0,[(1,4,220),(3,3,224)]),(0,[(1,1,2),(1,2,3)]),(0,[(1,1,2),(1,3,6),(1,2,3)]),(0,[(1,1,2),(1,2,4)]),(0,[(1,1,2),(1,4,6),(1,2,4)]),(0,[(1,1,2),(1,3,6)]),(6,[(1,1,2),(1,0,1)]),(0,[(1,1,2),(3,3,6)]),(1,[(3,3,6)]),(3,[(1,0,1),(1,3,12)]),(0,[(1,1,2),(1,3,12),(3,4,55)]),(3,[(1,3,12)]),(0,[(1,1,2),(3,3,12)]),(3,[(1,0,1),(3,3,12)]),(1,[(3,3,12)]),(0,[(1,1,2),(1,4,6)]),(10,[(1,1,2),(1,0,1)]),(0,[(1,1,2),(3,4,6)]),(1,[(3,4,6)]),(3,[(1,0,1),(1,4,12)]),(0,[(1,1,2),(1,4,12),(3,3,33)]),(3,[(1,4,12)]),(0,[(1,1,2),(3,4,12)]),(3,[(1,0,1),(3,4,12)]),(1,[(3,4,12)]),(0,[(1,1,3),(1,2,3)]),(0,[(1,1,2),(1,1,3),(1,2,3)]),(0,[(1,1,2),(1,1,3)]),(3,[(1,10,12),(1,1,3)]),(0,[(1,1,3),(3,2,6)]),(3,[(1,1,3),(1,0,1)]),(1,[(3,2,6)]),(6,[(1,1,2)]),(1,[(1,3,12),(3,2,55)]),(0,[(1,3,4),(1,1,3)]),(0,[(1,3,4),(1,4,6),(1,1,3)]),(0,[(1,4,6),(1,1,3)]),(0,[(3,4,6),(1,1,3)]),(6,[(1,0,1),(1,4,85)]),(0,[(1,1,3),(1,4,85),(3,2,88)]),(6,[(1,4,85)]),(0,[(1,1,3),(3,4,85)]),(6,[(1,0,1),(3,4,85)]),(1,[(3,4,85)]),(0,[(1,2,4),(1,1,4)]),(0,[(1,1,2),(1,2,4),(1,1,4)]),(0,[(1,1,2),(1,1,4)]),(3,[(1,10,12),(1,1,4)]),(0,[(3,2,6),(1,1,4)]),(10,[(1,1,2)]),(1,[(1,4,12),(3,2,33)]),(0,[(1,3,4),(1,1,4)]),(0,[(1,3,4),(1,3,6),(1,1,4)]),(0,[(1,3,6),(1,1,4)]),(0,[(3,3,6),(1,1,4)]),(10,[(1,1,3)]),(1,[(1,4,85),(3,3,88)]),(3,[(1,0,1),(1,3,10),(1,3,12)]),(0,[(1,2,3),(1,2,4)]),(0,[(1,3,4),(1,2,3),(1,2,4)]),(3,[(1,10,12)]),(0,[(1,3,6),(1,1,2),(1,2,3)]),(0,[(1,3,4),(1,2,3)]),(0,[(1,3,6),(1,2,3)]),(1,[(1,3,6),(1,2,3)]),(3,[(1,0,1),(1,4,6),(2,45,87)]),(0,[(1,2,3),(1,4,87)]),(3,[(1,4,87)]),(6,[(1,4,87)]),(0,[(1,2,3),(3,4,87)]),(3,[(3,4,87)]),(6,[(3,4,87)]),(10,[(1,1,2),(1,3,12),(3,0,55)]),(1,[(1,3,6),(1,12,17)]),(10,[(1,0,2),(1,3,10),(3,1,44)]),(3,[(1,0,1),(2,6,87)]),(0,[(1,3,10),(3,6,44)]),(3,[(1,0,1),(1,4,10),(1,4,12)]),(0,[(1,3,4),(1,2,4)]),(3,[(1,0,1),(1,3,6),(2,17,111)]),(0,[(1,2,4),(3,3,111)]),(3,[(3,3,111)]),(10,[(3,3,111)]),(0,[(1,4,6),(1,2,4)]),(1,[(1,4,6),(1,2,4)]),(6,[(1,1,2),(1,4,12),(3,0,33)]),(6,[(1,0,2),(1,4,10),(3,1,18)]),(3,[(1,4,10),(1,12,18)]),(3,[(1,0,1),(2,6,111)]),(1,[(1,4,12),(3,6,33)]),(0,[(1,1,2),(3,3,41)]),(1,[(1,0,2),(3,3,41)]),(3,[(1,10,12),(3,3,41)]),(0,[(1,1,2),(3,4,41)]),(1,[(1,0,2),(3,4,41)]),(3,[(1,10,12),(3,4,41)]),(0,[(1,3,6),(1,1,2)]),(6,[(1,0,1),(3,2,17)]),(10,[(1,0,1),(3,2,45)]),(6,[(1,0,1),(1,4,85),(1,4,220)]),(0,[(1,3,4),(3,1,14)]),(0,[(1,3,4),(3,2,14)]),(6,[(3,2,14)]),(10,[(3,2,14)]),(0,[(1,3,4),(1,3,6)]),(1,[(1,3,4),(1,3,6)]),(0,[(1,3,4),(1,3,6),(1,4,6)]),(0,[(1,3,4),(1,4,6)]),(1,[(1,3,4),(1,4,6)]),(6,[(1,0,1),(1,14,17)]),(3,[(0,0,1),(1,0,1)]),(6,[(1,0,1),(1,14,17),(3,2,26)]),(6,[(1,0,1),(3,14,17)]),(0,[(1,3,4),(3,6,14)]),(0,[(1,3,6),(3,2,17)]),(1,[(1,3,6),(3,2,17)]),(0,[(1,3,6),(3,4,17)]),(1,[(1,3,6),(3,4,17)]),(6,[(1,0,1),(3,4,17)]),(0,[(1,3,6),(1,4,6)]),(0,[(3,3,6),(1,2,43)]),(1,[(3,3,6),(1,2,43)]),(6,[(1,0,1),(1,2,43)]),(0,[(3,3,6),(1,4,43)]),(1,[(3,3,6),(1,4,43)]),(6,[(1,0,1),(1,4,43)]),(0,[(1,4,6),(3,2,45)]),(1,[(1,4,6),(3,2,45)]),(0,[(1,4,6),(3,3,45)]),(1,[(1,4,6),(3,3,45)]),(10,[(1,0,1),(3,3,45)]),(0,[(3,4,6),(1,2,47)]),(1,[(3,4,6),(1,2,47)]),(10,[(1,0,1),(1,2,47)]),(6,[(1,0,2),(1,1,2)]),(3,[(1,0,3)]),(1,[(1,0,2),(1,3,12),(1,0,3)]),(3,[(1,1,3),(1,0,3)]),(3,[(1,1,4)]),(6,[(1,1,4)]),(10,[(1,0,2),(1,0,3)]),(3,[(3,1,10),(1,0,3)]),(6,[(1,0,2),(3,1,10)]),(0,[(3,1,10)]),(0,[(1,3,6),(3,1,17)]),(10,[(1,0,2),(1,2,3),(1,0,3)]),(6,[(1,0,2),(1,4,10)]),(3,[(1,0,3),(1,4,220)]),(6,[(1,0,2),(1,2,4)]),(6,[(1,0,2),(1,2,4),(1,4,220)]),(3,[(1,3,4),(1,0,3)]),(3,[(1,3,4),(1,4,10),(1,0,3)]),(3,[(1,4,10),(1,0,3)]),(3,[(3,4,10),(1,0,3)]),(6,[(1,0,2),(3,4,10)]),(6,[(1,0,2),(1,4,220)]),(3,[(1,0,3),(3,4,220)]),(6,[(1,0,2),(3,4,220)]),(10,[(1,0,2),(1,1,2)]),(3,[(1,0,4)]),(1,[(1,0,2),(1,4,12),(1,0,4)]),(3,[(1,1,3)]),(6,[(1,0,2),(1,0,4)]),(3,[(1,1,4),(1,0,4)]),(3,[(3,1,10),(1,0,4)]),(10,[(1,0,2),(3,1,10)]),(0,[(1,4,6),(3,1,45)]),(10,[(1,0,2),(1,2,3)]),(6,[(1,0,2),(1,4,87),(1,0,4)]),(6,[(1,0,2),(1,2,4),(1,0,4)]),(10,[(1,0,2),(1,3,10)]),(3,[(1,3,4),(1,0,4)]),(3,[(1,3,4),(1,3,10),(1,0,4)]),(3,[(1,3,10),(1,0,4)]),(3,[(3,3,10),(1,0,4)]),(10,[(1,0,2),(3,3,10)]),(0,[(1,1,2),(1,3,10),(1,1,3)]),(0,[(1,1,2),(1,4,10),(1,1,4)]),(0,[(1,1,2),(1,3,10)]),(6,[(1,1,2),(1,0,2)]),(0,[(1,1,2),(3,3,10)]),(3,[(3,3,10)]),(1,[(1,0,2),(1,3,12)]),(1,[(1,0,2),(3,3,12)]),(3,[(3,3,12)]),(0,[(1,1,2),(1,4,10)]),(10,[(1,1,2),(1,0,2)]),(0,[(1,1,2),(3,4,10)]),(3,[(3,4,10)]),(1,[(1,0,2),(1,4,12)]),(1,[(1,0,2),(3,4,12)]),(3,[(3,4,12)]),(1,[(1,0,2),(1,3,6),(1,3,12)]),(0,[(1,1,3),(1,1,4)]),(0,[(1,3,4),(1,1,3),(1,1,4)]),(0,[(1,3,10),(1,1,3)]),(3,[(1,3,10),(1,1,3)]),(1,[(1,0,2),(1,4,10),(2,18,85)]),(6,[(3,4,85)]),(1,[(1,0,2),(2,10,85)]),(0,[(1,3,6),(3,10,17)]),(1,[(1,0,2),(1,4,12),(1,4,6)]),(0,[(1,4,10),(1,1,2),(1,1,4)]),(1,[(1,0,2),(1,3,10),(2,44,145)]),(10,[(1,1,3),(3,3,88)]),(0,[(1,4,10),(1,1,4)]),(3,[(1,4,10),(1,1,4)]),(1,[(1,0,2),(2,10,145)]),(3,[(1,4,12),(3,10,33)]),(0,[(1,4,10),(1,1,2)]),(3,[(3,1,10)]),(0,[(1,2,3),(3,1,10)]),(1,[(1,2,3),(1,0,2)]),(0,[(1,2,4),(3,1,10)]),(1,[(1,2,4),(1,0,2)]),(6,[(1,0,2),(3,1,44)]),(10,[(1,0,2),(3,1,18)]),(3,[(1,3,12),(3,1,55)]),(0,[(1,3,4),(1,4,10),(1,2,3)]),(0,[(1,4,10),(1,2,3)]),(0,[(3,4,10),(1,2,3)]),(6,[(1,0,2),(1,4,87)]),(0,[(1,2,3),(1,4,87),(3,1,90)]),(6,[(1,0,2),(3,4,87)]),(3,[(1,4,12),(3,1,33)]),(0,[(1,3,4),(1,3,10),(1,2,4)]),(0,[(1,3,10),(1,2,4)]),(0,[(3,3,10),(1,2,4)]),(10,[(1,0,2),(3,3,111)]),(6,[(1,0,2),(1,4,87),(1,4,220)]),(6,[(3,1,14)]),(10,[(3,1,14)]),(0,[(1,3,4),(1,3,10)]),(3,[(1,3,4),(1,3,10)]),(0,[(1,3,4),(1,4,10),(1,3,10)]),(0,[(1,3,4),(1,4,10)]),(3,[(1,3,4),(1,4,10)]),(1,[(1,2,3),(1,4,87),(3,0,90)]),(10,[(1,0,2),(1,14,18)]),(1,[(0,0,2),(1,0,2)]),(6,[(1,0,2),(1,4,10),(3,1,28)]),(10,[(1,0,2),(3,14,18)]),(0,[(1,3,4),(3,10,14)]),(0,[(1,3,10),(3,1,44)]),(3,[(1,3,10),(3,1,44)]),(0,[(1,3,10),(3,4,44)]),(3,[(1,3,10),(3,4,44)]),(6,[(1,0,2),(3,4,44)]),(0,[(1,4,10),(1,3,10)]),(0,[(3,3,10),(1,1,54)]),(6,[(1,0,2),(1,1,54)]),(3,[(3,3,10),(1,1,54)]),(0,[(3,3,10),(1,4,54)]),(3,[(3,3,10),(1,4,54)]),(6,[(1,0,2),(1,4,54)]),(0,[(1,4,10),(3,1,18)]),(3,[(1,4,10),(3,1,18)]),(0,[(1,4,10),(3,3,18)]),(3,[(1,4,10),(3,3,18)]),(10,[(1,0,2),(3,3,18)]),(0,[(3,4,10),(1,1,32)]),(10,[(1,0,2),(1,1,32)]),(3,[(3,4,10),(1,1,32)]),(0,[(3,4,10),(1,3,32)]),(3,[(3,4,10),(1,3,32)]),(10,[(1,0,2),(1,3,32)]),(1,[(1,0,3),(1,0,4)]),(1,[(1,3,4),(1,0,3),(1,0,4)]),(6,[(1,0,4)]),(3,[(1,0,3),(1,0,4)]),(10,[(1,1,3),(1,0,3)]),(1,[(1,4,85),(1,0,3),(1,0,4)]),(6,[(1,1,4),(1,0,4)]),(10,[(1,2,3),(1,0,3)]),(3,[(1,4,87),(1,0,3),(1,0,4)]),(6,[(1,2,4),(1,0,4)]),(3,[(1,3,4),(1,0,3),(1,0,4)]),(0,[(1,1,2),(1,3,6),(1,3,10)]),(1,[(1,3,12),(1,0,3)]),(3,[(1,3,12),(1,0,3)]),(0,[(1,1,2),(1,4,12),(2,33,220)]),(6,[(3,4,220)]),(10,[(0,0,3),(1,0,3)]),(0,[(1,1,2),(2,12,220)]),(1,[(1,3,6),(3,12,17)]),(0,[(1,1,3),(1,1,4),(1,4,220)]),(6,[(1,1,2),(3,2,55)]),(3,[(1,1,3),(1,3,10)]),(6,[(1,0,2),(3,2,44)]),(1,[(1,4,85),(1,0,3)]),(1,[(3,4,85),(1,0,3)]),(0,[(1,1,3),(1,4,220)]),(0,[(1,1,3),(3,4,220)]),(1,[(1,4,6),(1,4,85),(1,0,3)]),(0,[(1,3,6),(1,1,4),(1,4,220)]),(10,[(1,1,2),(3,2,33)]),(0,[(1,1,4),(1,4,220)]),(6,[(1,1,4),(1,4,220)]),(10,[(1,0,1),(1,3,6),(3,2,26)]),(0,[(1,4,6),(2,45,220)]),(1,[(1,3,6),(2,17,145)]),(0,[(1,3,6),(1,3,10)]),(0,[(1,3,6),(1,4,220)]),(6,[(1,0,1),(3,1,17)]),(1,[(1,2,3),(1,3,6)]),(6,[(1,1,2),(3,1,55)]),(0,[(1,2,3),(1,2,4),(1,4,220)]),(3,[(1,4,87),(1,0,3)]),(3,[(3,4,87),(1,0,3)]),(0,[(1,2,3),(1,4,220)]),(0,[(1,2,3),(3,4,220)]),(3,[(1,4,10),(1,4,87),(1,0,3)]),(10,[(1,1,2),(3,1,33)]),(0,[(1,3,10),(1,2,4),(1,4,220)]),(0,[(1,2,4),(1,4,220)]),(6,[(1,2,4),(1,4,220)]),(10,[(1,0,2),(1,14,18),(3,1,28)]),(6,[(1,4,87),(2,90,220)]),(3,[(1,3,10),(2,44,111)]),(0,[(1,3,10),(1,4,220)]),(3,[(1,3,10),(1,4,134)]),(10,[(3,1,14),(1,0,3)]),(10,[(3,2,14),(1,0,3)]),(3,[(1,0,3),(1,4,220),(0,1,224)]),(1,[(1,0,3),(1,4,220),(0,2,224)]),(1,[(1,4,12),(1,0,2),(1,0,4)]),(0,[(1,1,2),(1,4,10),(1,4,6)]),(0,[(1,1,2),(1,3,12),(2,55,286)]),(10,[(1,0,3),(3,3,224)]),(1,[(1,4,12),(1,0,4)]),(3,[(1,4,12),(1,0,4)]),(6,[(0,0,4),(1,0,4)]),(0,[(1,1,2),(2,12,286)]),(3,[(1,4,10),(3,12,18)]),(1,[(1,3,6),(1,4,85),(1,0,4)]),(0,[(1,4,6),(1,1,3),(1,4,220)]),(10,[(1,0,2),(3,2,18)]),(1,[(1,4,85),(1,0,4)]),(6,[(1,4,85),(1,0,4)]),(0,[(1,3,6),(2,17,286)]),(1,[(1,4,6),(2,45,85)]),(0,[(1,4,10),(1,4,6)]),(0,[(1,4,6),(1,4,220)]),(10,[(1,0,1),(3,1,45)]),(1,[(1,2,4),(1,4,6)]),(3,[(1,3,10),(1,4,87),(1,0,4)]),(0,[(1,4,10),(1,2,3),(1,4,220)]),(3,[(1,4,87),(1,0,4)]),(6,[(1,4,87),(1,0,4)]),(0,[(1,2,3),(2,87,286)]),(3,[(1,4,10),(2,18,87)]),(3,[(3,3,111),(1,0,4)]),(0,[(1,4,10),(1,4,220)]),(6,[(3,1,14),(1,0,4)]),(6,[(3,2,14),(1,0,4)]),(3,[(1,10,12),(1,3,12)]),(1,[(1,4,12),(1,0,2)]),(3,[(1,10,12),(1,4,12)]),(1,[(3,0,12)]),(3,[(3,0,12)]),(3,[(1,1,3),(3,0,12)]),(0,[(1,1,3),(1,1,2)]),(6,[(1,1,2),(3,0,12)]),(3,[(1,1,4),(3,0,12)]),(0,[(1,1,4),(1,1,2)]),(10,[(1,1,2),(3,0,12)]),(1,[(1,2,3),(3,0,12)]),(0,[(1,2,3),(1,1,2)]),(1,[(1,2,4),(3,0,12)]),(0,[(1,2,4),(1,1,2)]),(6,[(1,1,2),(3,0,55)]),(10,[(1,1,2),(3,0,33)]),(10,[(1,1,2),(1,1,3)]),(1,[(1,3,6),(3,0,17)]),(10,[(1,1,2),(1,1,3),(1,2,3)]),(6,[(1,1,2),(1,4,12)]),(10,[(1,1,2),(1,2,3),(1,1,3)]),(3,[(1,1,3),(1,4,85)]),(1,[(1,2,3),(1,4,87)]),(6,[(1,1,2),(1,2,4)]),(6,[(1,1,2),(1,4,85),(1,2,4)]),(3,[(1,3,4),(1,1,3)]),(3,[(1,3,4),(1,4,12),(1,1,3)]),(3,[(1,4,12),(1,1,3)]),(3,[(3,4,12),(1,1,3)]),(6,[(1,1,2),(3,4,12)]),(6,[(1,1,2),(1,4,85)]),(3,[(1,1,3),(3,4,85)]),(6,[(1,1,2),(3,4,85)]),(6,[(1,1,2),(1,1,4)]),(1,[(1,4,6),(3,0,45)]),(10,[(1,1,2),(1,2,3)]),(6,[(1,1,2),(1,4,87),(1,1,4)]),(6,[(1,1,2),(1,2,4),(1,1,4)]),(10,[(1,1,2),(1,3,12)]),(3,[(1,3,4),(1,1,4)]),(3,[(1,3,4),(1,3,12),(1,1,4)]),(3,[(1,3,12),(1,1,4)]),(3,[(3,3,12),(1,1,4)]),(10,[(1,1,2),(3,3,12)]),(3,[(1,3,10),(3,0,44)]),(1,[(1,3,4),(1,2,3)]),(1,[(1,3,4),(1,4,12),(1,2,3)]),(1,[(1,4,12),(1,2,3)]),(1,[(3,4,12),(1,2,3)]),(6,[(1,1,2),(1,4,87)]),(1,[(1,2,3),(3,4,87)]),(6,[(1,1,2),(3,4,87)]),(3,[(1,4,10),(3,0,18)]),(1,[(1,3,4),(1,2,4)]),(1,[(1,3,4),(1,3,12),(1,2,4)]),(1,[(1,3,12),(1,2,4)]),(1,[(3,3,12),(1,2,4)]),(1,[(1,2,4),(3,3,111)]),(10,[(1,1,2),(3,3,111)]),(1,[(1,3,4),(3,0,14)]),(6,[(3,0,14)]),(10,[(3,0,14)]),(6,[(1,1,2),(1,4,85),(1,4,87)]),(1,[(1,3,4),(3,2,14)]),(1,[(1,3,4),(1,3,12)]),(3,[(1,3,4),(1,3,12)]),(1,[(1,3,4),(1,4,12),(1,3,12)]),(1,[(1,3,4),(1,4,12)]),(3,[(1,3,4),(1,4,12)]),(1,[(1,3,4),(1,12,14)]),(3,[(1,3,4),(1,12,14)]),(6,[(1,1,2),(1,12,14)]),(10,[(1,1,2),(1,12,14)]),(1,[(1,3,4),(1,12,14),(3,0,19)]),(6,[(1,1,2),(1,12,14),(3,0,19)]),(6,[(1,1,2),(2,12,14)]),(1,[(1,3,4),(3,12,14)]),(10,[(1,1,2),(1,3,12),(0,0,55)]),(1,[(1,3,12),(3,0,55)]),(3,[(1,3,12),(3,0,55)]),(1,[(1,3,12),(3,4,55)]),(3,[(1,3,12),(3,4,55)]),(6,[(1,1,2),(3,4,55)]),(1,[(1,4,12),(1,3,12)]),(6,[(1,1,2),(1,0,59)]),(1,[(3,3,12),(1,0,59)]),(3,[(3,3,12),(1,0,59)]),(1,[(3,3,12),(1,4,59)]),(3,[(3,3,12),(1,4,59)]),(6,[(1,1,2),(1,4,59)]),(6,[(1,1,2),(1,4,12),(0,0,33)]),(1,[(1,4,12),(3,0,33)]),(3,[(1,4,12),(3,0,33)]),(1,[(1,4,12),(3,3,33)]),(3,[(1,4,12),(3,3,33)]),(10,[(1,1,2),(3,3,33)]),(10,[(1,1,2),(1,0,38)]),(1,[(3,4,12),(1,0,38)]),(3,[(3,4,12),(1,0,38)]),(1,[(3,4,12),(1,3,38)]),(3,[(3,4,12),(1,3,38)]),(10,[(1,1,2),(1,3,38)]),(1,[(1,3,6),(1,3,12)]),(1,[(1,3,6),(1,4,85)]),(6,[(1,0,1),(3,0,17)]),(0,[(1,1,4),(1,3,6)]),(0,[(1,2,3),(1,3,6)]),(3,[(1,1,3),(1,1,4)]),(0,[(1,1,3),(1,4,6)]),(10,[(1,1,3),(1,2,3)]),(3,[(1,1,3),(1,4,87),(1,1,4)]),(6,[(1,2,4),(1,1,4)]),(3,[(1,1,3),(1,4,12)]),(3,[(1,3,4),(1,1,3),(1,1,4)]),(0,[(1,1,3),(1,3,10)]),(6,[(1,0,2),(3,0,44)]),(1,[(1,2,3),(1,2,4)]),(1,[(1,2,3),(1,4,85),(1,2,4)]),(1,[(1,2,3),(1,4,85)]),(10,[(1,2,3),(1,1,3)]),(1,[(1,2,3),(3,4,85)]),(3,[(1,1,3),(1,4,87)]),(3,[(1,1,3),(3,4,87)]),(10,[(1,0,2),(3,0,18)]),(3,[(1,4,12),(1,1,3),(1,4,87)]),(1,[(1,3,12),(1,4,85),(1,2,4)]),(1,[(1,4,85),(1,2,4)]),(6,[(1,4,85),(1,2,4)]),(3,[(1,3,4),(1,12,14),(3,0,19)]),(3,[(1,1,3),(2,85,111)]),(6,[(1,4,87),(3,85,90)]),(1,[(1,3,12),(1,4,85)]),(3,[(1,3,12),(1,4,127)]),(0,[(1,1,3),(1,3,4)]),(10,[(1,1,3),(3,0,14)]),(10,[(1,1,3),(3,2,14)]),(3,[(1,1,3),(1,3,4)]),(3,[(1,1,3),(1,4,85),(0,0,88)]),(1,[(1,4,85),(3,2,88)]),(6,[(1,4,85),(3,2,88)]),(10,[(1,1,3),(3,2,88)]),(1,[(3,4,85),(1,2,89)]),(6,[(3,4,85),(1,2,89)]),(10,[(1,1,3),(1,2,89)]),(1,[(1,4,12),(1,4,6)]),(1,[(1,4,6),(1,4,85)]),(10,[(1,0,1),(3,0,45)]),(0,[(1,2,4),(1,4,6)]),(3,[(1,3,12),(1,4,87),(1,1,4)]),(1,[(1,4,12),(1,2,3),(1,4,85)]),(3,[(1,4,87),(1,1,4)]),(6,[(1,4,87),(1,1,4)]),(1,[(1,2,3),(2,87,145)]),(6,[(1,4,85),(3,87,88)]),(0,[(1,1,4),(1,4,10)]),(3,[(3,3,111),(1,1,4)]),(6,[(1,2,4),(1,4,85)]),(1,[(1,4,12),(1,4,85)]),(3,[(1,4,12),(1,3,160)]),(0,[(1,1,4),(1,3,4)]),(6,[(1,1,4),(3,0,14)]),(6,[(3,2,14),(1,1,4)]),(6,[(1,4,85),(1,2,123)]),(3,[(1,3,10),(1,3,12)]),(3,[(1,3,10),(1,4,87)]),(0,[(1,3,10),(1,1,321)]),(0,[(1,2,4),(1,3,10)]),(0,[(1,3,10),(1,4,321)]),(3,[(1,3,12),(1,4,87)]),(1,[(1,2,4),(1,3,12)]),(1,[(1,3,12),(1,4,172)]),(0,[(1,2,3),(1,4,10)]),(1,[(1,2,3),(1,4,12)]),(1,[(1,3,4),(1,2,3),(1,2,4)]),(0,[(1,2,3),(1,3,4)]),(10,[(1,2,3),(3,0,14)]),(3,[(1,3,4),(3,0,14)]),(3,[(1,3,4),(3,1,14)]),(10,[(1,2,3),(3,1,14)]),(1,[(1,2,3),(1,3,4)]),(1,[(1,2,3),(1,4,87),(0,0,90)]),(3,[(1,4,87),(3,0,90)]),(6,[(1,4,87),(3,0,90)]),(10,[(1,2,3),(3,0,90)]),(3,[(1,4,87),(3,1,90)]),(6,[(1,4,87),(3,1,90)]),(10,[(1,2,3),(3,1,90)]),(10,[(1,2,3),(1,0,94)]),(3,[(3,4,87),(1,0,94)]),(6,[(3,4,87),(1,0,94)]),(3,[(3,4,87),(1,1,94)]),(6,[(3,4,87),(1,1,94)]),(10,[(1,2,3),(1,1,94)]),(3,[(1,4,10),(1,4,12)]),(3,[(1,4,10),(1,4,87)]),(0,[(1,4,10),(1,1,336)]),(0,[(1,4,10),(1,3,336)]),(3,[(1,4,12),(1,4,87)]),(1,[(1,4,12),(1,3,186)]),(0,[(1,2,4),(1,3,4)]),(6,[(1,2,4),(3,0,14)]),(6,[(1,2,4),(3,1,14)]),(1,[(1,2,4),(1,3,4)]),(6,[(1,2,4),(1,0,122)]),(3,[(3,3,111),(1,0,122)]),(10,[(3,3,111),(1,0,122)]),(3,[(3,3,111),(1,1,122)]),(10,[(3,3,111),(1,1,122)]),(6,[(1,2,4),(1,1,122)]),(6,[(1,4,85),(1,4,220)]),(6,[(1,4,87),(1,4,220)]),(0,[(1,3,4),(1,1,323)]),(6,[(3,0,14),(1,1,323)]),(10,[(3,0,14),(1,1,323)]),(0,[(1,3,4),(1,2,323)]),(6,[(3,0,14),(1,2,323)]),(10,[(3,0,14),(1,2,323)]),(6,[(1,4,85),(1,4,87)]),(6,[(3,1,14),(1,2,174)]),(10,[(3,1,14),(1,2,174)]),(1,[(1,3,4),(1,2,174)]),(3,[(1,3,4),(1,0,130)]),(6,[(3,2,14),(1,0,130)]),(10,[(3,2,14),(1,0,130)]),(6,[(3,2,14),(1,1,130)]),(10,[(3,2,14),(1,1,130)]),(3,[(1,3,4),(1,1,130)])]
def h26Pools : BT (Option BoundPool) := buildPoolsBT 10 h26W h26R h26Slices h26Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice14 : Slice h26R h26G (subcubeFast 48 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice13 : Slice h26R h26G (subcubeFast 40 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice12 : Slice h26R h26G (subcubeFast 36 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice11 : Slice h26R h26G (subcubeFast 34 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice10 : Slice h26R h26G (subcubeFast 32 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice9 : Slice h26R h26G (subcubeFast 24 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice8 : Slice h26R h26G (subcubeFast 20 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice7 : Slice h26R h26G (subcubeFast 18 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice6 : Slice h26R h26G (subcubeFast 16 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice5 : Slice h26R h26G (subcubeFast 12 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice4 : Slice h26R h26G (subcubeFast 10 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice3 : Slice h26R h26G (subcubeFast 8 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice2 : Slice h26R h26G (subcubeFast 6 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice1 : Slice h26R h26G (subcubeFast 4 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Slice0 : Slice h26R h26G (subcubeFast 2 0) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h26R h26G p.1 p.2) h26Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h26R h26G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h26Slice0) (forall_cons (fun _ h => by cases h; exact h26Slice1) (forall_cons (fun _ h => by cases h; exact h26Slice2) (forall_cons (fun _ h => by cases h; exact h26Slice3) (forall_cons (fun _ h => by cases h; exact h26Slice4) (forall_cons (fun _ h => by cases h; exact h26Slice5) (forall_cons (fun _ h => by cases h; exact h26Slice6) (forall_cons (fun _ h => by cases h; exact h26Slice7) (forall_cons (fun _ h => by cases h; exact h26Slice8) (forall_cons (fun _ h => by cases h; exact h26Slice9) (forall_cons (fun _ h => by cases h; exact h26Slice10) (forall_cons (fun _ h => by cases h; exact h26Slice11) (forall_cons (fun _ h => by cases h; exact h26Slice12) (forall_cons (fun _ h => by cases h; exact h26Slice13) (forall_cons (fun _ h => by cases h; exact h26Slice14) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h26R h26G c) h26Pools := buildPoolsBT_sound h26SlicesOk
def h26Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G (3 - 1) xs.toFinset) h26Empty := trivial
def h26Block3_0 : List NodeSpec := nodesWithIdentity [([12,14,17,18],[4]),([10,14,17,33],[5]),([12,14,44,45],[6]),([6,14,33,44],[5]),([10,14,45,55],[7]),([6,14,18,55],[7]),([10,45,85,90],[11]),([10,47,85,94],[]),([6,18,87,88],[12]),([6,32,87,89],[]),([44,45,85,111],[6]),([6,44,88,111],[12]),([17,18,87,145],[4]),([10,17,90,145],[11]),([10,43,122,145],[]),([6,54,111,123],[]),([12,45,90,220],[11]),([12,47,94,220],[]),([6,33,87,224],[5]),([6,38,87,225],[]),([45,55,111,220],[7]),([6,55,111,224],[7]),([41,88,111,220],[12]),([41,85,111,224],[13]),([41,90,145,220],[11]),([41,87,145,224],[13]),([125,130,145,220],[]),([6,14,134,160],[]),([17,33,87,286],[5]),([12,17,90,286],[11]),([12,43,122,286],[]),([6,59,111,239],[]),([41,87,88,286],[12]),([41,85,90,286],[11]),([85,125,130,286],[]),([6,14,127,132],[]),([3,4,40,66],[]),([2,4,66,248],[]),([2,3,66,302],[]),([3,6,40,99],[]),([2,6,99,248],[]),([2,3,6,393],[]),([1,87,99,394],[]),([0,87,99,395],[]),([0,1,87,396],[]),([4,6,40,156],[]),([2,6,156,302],[]),([2,4,6,409],[]),([1,111,156,410],[]),([0,111,156,411],[]),([0,1,111,412],[]),([1,2,255,413],[]),([0,2,255,415],[]),([0,1,252,255],[]),([3,4,6,433],[]),([4,6,195,248],[]),([3,6,195,302],[]),([12,18,88,220],[12]),([12,32,89,220],[]),([10,33,85,224],[5]),([10,38,85,225],[]),([18,55,145,220],[7]),([10,55,145,224],[7]),([111,171,174,220],[]),([10,14,178,186],[]),([33,44,85,286],[5]),([12,44,88,286],[12]),([12,54,123,286],[]),([10,59,145,239],[]),([87,171,174,286],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test3_0 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Empty 3 h26Block3_0 = true := by decide +kernel
def h26Block3_1 : List NodeSpec := nodesWithIdentity [([10,14,172,175],[]),([3,4,52,63],[]),([1,4,63,227],[]),([1,3,63,294],[]),([3,10,52,99],[]),([1,10,99,227],[]),([1,3,10,461],[]),([2,85,99,231],[]),([0,85,99,226],[]),([0,2,85,462],[]),([4,10,52,156],[]),([1,10,156,294],[]),([1,4,10,469],[]),([2,145,156,287],[]),([0,145,156,235],[]),([0,2,145,470],[]),([3,4,10,479],[]),([4,10,197,227],[]),([3,10,197,294],[]),([127,132,145,220],[]),([85,134,160,286],[]),([87,178,186,286],[]),([111,172,175,220],[]),([3,4,57,65],[]),([0,4,65,97],[]),([0,3,65,155],[]),([3,12,57,99],[]),([0,12,97,99],[]),([0,3,12,494],[]),([2,99,104,220],[]),([1,95,99,220],[]),([1,2,220,495],[]),([4,12,57,156],[]),([0,12,155,156],[]),([0,4,12,509],[]),([2,146,156,286],[]),([1,113,156,286],[]),([1,2,286,510],[]),([85,111,320,323],[]),([87,145,320,323],[]),([12,14,328,336],[]),([12,14,321,324],[]),([87,145,328,336],[]),([85,111,321,324],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test3_1 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Empty 3 h26Block3_1 = true := by decide +kernel
def h26Nodes3 : List NodeSpec := h26Block3_0 ++ h26Block3_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Check3 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Empty 3 h26Nodes3 = true := by
  unfold h26Nodes3 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h26Test3_0,h26Test3_1⟩
def h26Bucket3 : BT (List (List Nat)) := buildBucketsBT h26W h26Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G 3 xs.toFinset) h26Bucket3 := buildBucketsBT_sound (by decide) h26Pairs h26WOk h26PoolsOk h26AutosOk h26EmptyOk h26Check3
def h26Block4_0 : List NodeSpec := nodesWithIdentity [([4,10,12,14,17],[]),([4,6,12,14,44],[]),([4,6,10,14,55],[]),([3,10,12,14,45],[]),([3,6,12,14,18],[]),([3,6,10,14,33],[]),([3,4,10,12,26],[10]),([3,4,6,12,28],[1]),([3,4,6,10,19],[0]),([3,4,12,17,18],[4]),([3,4,12,17,32],[]),([3,4,10,17,33],[5]),([3,4,10,17,38],[]),([3,4,10,12,39],[]),([3,4,10,12,17],[10]),([3,4,12,18,43],[]),([3,4,12,32,43],[]),([3,4,10,33,43],[]),([3,4,10,38,43],[]),([3,4,10,12,75],[]),([3,4,12,44,45],[6]),([3,4,12,44,47],[]),([3,4,6,33,44],[5]),([3,4,6,38,44],[]),([3,4,6,12,51],[]),([3,4,6,12,44],[1]),([3,4,12,45,54],[]),([3,4,12,47,54],[]),([3,4,6,33,54],[]),([3,4,6,38,54],[]),([3,4,6,12,77],[]),([3,4,10,45,55],[7]),([3,4,10,47,55],[]),([3,4,6,18,55],[7]),([3,4,6,32,55],[]),([3,4,6,10,56],[]),([3,4,6,10,55],[0]),([3,4,10,45,59],[]),([3,4,10,47,59],[]),([3,4,6,18,59],[]),([3,4,6,32,59],[]),([3,4,6,10,78],[]),([3,4,10,12,60],[]),([3,4,10,12,72],[]),([3,4,10,12,45],[10]),([3,4,6,12,61],[]),([3,4,6,12,70],[]),([3,4,6,12,18],[1]),([3,4,6,10,62],[]),([3,4,6,10,71],[]),([3,4,6,10,33],[0]),([4,10,45,85,87],[22]),([4,10,47,85,87],[11]),([4,6,18,85,87],[4]),([4,6,32,85,87],[12]),([4,6,10,87,88],[12]),([4,6,10,87,89],[12]),([4,6,10,85,90],[11]),([4,6,10,85,94],[11]),([6,10,14,85,111],[]),([4,6,44,85,111],[]),([3,10,45,85,111],[]),([3,6,10,88,111],[12]),([2,10,14,45,85],[]),([2,6,14,18,85],[4]),([2,4,6,28,85],[1]),([2,4,44,45,85],[6]),([2,4,44,47,85],[]),([2,4,6,51,85],[]),([2,4,6,44,88],[12])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_0 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_0 = true := by decide +kernel
def h26Block4_1 : List NodeSpec := nodesWithIdentity [([2,4,6,44,89],[]),([2,4,6,44,85],[1]),([2,3,6,18,88],[12]),([2,4,6,70,85],[1]),([2,3,6,32,89],[]),([3,4,6,10,138],[0]),([6,10,14,87,145],[]),([4,10,17,87,145],[]),([3,6,18,87,145],[]),([3,6,10,90,145],[11]),([3,10,17,111,145],[33]),([3,10,43,111,145],[11]),([3,6,44,111,145],[6]),([3,6,54,111,145],[12]),([3,6,10,122,145],[11]),([3,6,10,111,123],[12]),([2,10,14,17,145],[]),([2,6,14,44,145],[6]),([2,3,6,28,145],[1]),([2,3,17,18,145],[4]),([2,3,18,43,145],[]),([2,4,6,54,123],[]),([2,3,6,77,145],[1]),([3,4,6,10,166],[0]),([2,3,6,18,123],[]),([2,3,6,61,145],[]),([2,3,6,18,145],[1]),([1,10,14,45,87],[22]),([1,6,14,18,87],[]),([1,4,10,26,87],[10]),([1,4,17,18,87],[4]),([1,4,17,32,87],[]),([1,4,10,39,87],[]),([1,4,10,17,90],[11]),([1,4,10,17,94],[]),([1,4,10,17,87],[10]),([1,3,10,45,90],[11]),([1,4,10,72,87],[10]),([1,3,10,47,94],[]),([3,4,6,10,182],[0]),([1,10,14,17,111],[33]),([1,6,14,44,111],[]),([1,3,10,26,111],[10]),([1,4,10,43,122],[]),([1,3,10,75,111],[10]),([1,3,44,45,111],[6]),([1,3,45,54,111],[]),([3,4,6,10,190],[0]),([1,3,10,45,122],[]),([1,3,10,60,111],[]),([1,3,10,45,111],[10]),([1,2,14,17,18],[4]),([1,2,14,44,45],[6]),([4,12,45,87,220],[22]),([4,12,47,87,220],[11]),([4,6,33,87,220],[5]),([4,6,38,87,220],[5]),([4,6,12,90,220],[11]),([4,6,12,94,220],[11]),([4,6,12,87,224],[13]),([4,6,12,87,225],[5]),([6,12,14,111,220],[]),([4,6,55,111,220],[]),([3,12,45,111,220],[]),([3,6,12,111,224],[13]),([2,12,14,45,220],[]),([2,6,14,33,220],[5]),([2,4,6,19,220],[0]),([2,4,45,55,220],[7]),([2,4,47,55,220],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_1 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_1 = true := by decide +kernel
def h26Block4_2 : List NodeSpec := nodesWithIdentity [([2,4,6,56,220],[]),([2,4,6,55,224],[7]),([2,4,6,55,225],[]),([2,4,6,55,220],[0]),([2,3,6,33,224],[5]),([2,4,6,71,220],[0]),([2,3,6,38,225],[]),([3,4,6,12,136],[1]),([4,41,85,111,220],[]),([2,45,85,111,220],[]),([2,6,88,111,220],[]),([2,6,85,111,224],[]),([2,4,24,85,220],[81]),([2,4,85,220,247],[]),([2,4,41,88,220],[12]),([2,4,41,89,220],[]),([2,4,41,85,224],[13]),([2,4,41,85,225],[]),([2,4,41,85,220],[81]),([2,4,88,125,220],[]),([2,4,89,125,220],[]),([2,4,85,210,220],[]),([2,4,85,125,224],[]),([2,4,85,125,225],[]),([2,4,45,127,220],[]),([2,4,47,127,220],[]),([2,4,6,128,220],[]),([2,4,6,127,224],[]),([2,4,6,127,225],[]),([2,4,45,85,134],[]),([2,4,47,85,134],[]),([2,4,6,88,134],[]),([2,4,6,89,134],[]),([2,4,6,85,240],[]),([2,4,85,131,220],[]),([2,4,85,135,220],[]),([2,4,45,85,220],[81]),([2,4,6,137,220],[]),([2,4,6,138,220],[]),([2,4,6,88,220],[0]),([2,4,6,85,133],[]),([2,4,6,85,136],[]),([2,4,6,85,224],[1]),([6,87,111,145,220],[]),([4,41,87,145,220],[]),([2,6,90,145,220],[11]),([2,6,87,145,224],[]),([3,41,111,145,220],[]),([2,14,41,145,220],[88]),([2,3,41,145,224],[13]),([2,14,125,145,220],[11]),([2,3,125,145,224],[]),([3,4,6,134,160],[]),([2,6,14,160,220],[5]),([2,4,6,161,220],[0]),([2,3,6,160,224],[]),([2,6,14,134,145],[5]),([2,3,6,145,240],[1]),([2,6,130,145,220],[11]),([2,3,6,133,145],[]),([2,3,6,145,224],[1]),([1,45,87,111,220],[22]),([1,6,87,111,224],[]),([1,4,24,87,220],[81]),([1,4,87,220,247],[]),([1,4,41,90,220],[11]),([1,4,41,94,220],[]),([1,4,41,87,224],[13]),([1,4,41,87,225],[]),([1,4,41,87,220],[81])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_2 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_2 = true := by decide +kernel
def h26Block4_3 : List NodeSpec := nodesWithIdentity [([1,2,45,90,220],[11]),([1,4,87,135,220],[81]),([1,2,47,94,220],[]),([2,4,6,182,220],[0]),([1,14,41,111,220],[88]),([1,3,41,111,224],[13]),([1,2,14,24,220],[81]),([4,41,85,87,220],[]),([2,4,41,220,266],[81]),([1,4,41,220,263],[81]),([1,2,15,220,247],[]),([1,2,41,220,264],[]),([1,4,125,130,220],[]),([1,2,14,210,220],[81]),([2,4,6,134,141],[]),([1,2,14,45,134],[]),([2,4,6,220,271],[0]),([1,2,45,130,220],[]),([1,2,14,131,220],[]),([1,2,14,45,220],[81]),([3,4,6,82,133],[]),([6,12,14,87,286],[]),([4,12,17,87,286],[]),([3,6,33,87,286],[]),([3,6,12,90,286],[11]),([3,12,17,111,286],[33]),([3,12,43,111,286],[11]),([3,6,55,111,286],[7]),([3,6,59,111,286],[7]),([3,6,12,122,286],[11]),([3,6,12,111,239],[7]),([2,12,14,17,286],[]),([2,6,14,55,286],[7]),([2,3,6,19,286],[0]),([2,3,17,33,286],[5]),([2,3,33,43,286],[]),([2,4,6,59,239],[]),([2,3,6,78,286],[0]),([3,4,6,12,169],[1]),([2,3,6,33,239],[]),([2,3,6,62,286],[]),([2,3,6,33,286],[0]),([6,85,87,111,286],[]),([4,41,85,87,286],[]),([2,6,87,88,286],[]),([2,6,85,90,286],[11]),([3,41,85,111,286],[]),([2,14,41,85,286],[88]),([2,3,41,88,286],[12]),([2,14,85,125,286],[11]),([2,3,88,125,286],[]),([3,4,6,127,132],[]),([2,6,14,127,286],[7]),([2,3,6,128,286],[0]),([2,6,14,85,132],[7]),([2,4,6,85,258],[1]),([2,3,6,88,132],[]),([2,6,85,130,286],[11]),([2,3,6,137,286],[]),([2,3,6,88,286],[0]),([3,41,87,145,286],[]),([2,17,87,145,286],[]),([2,3,22,145,286],[124]),([2,3,145,254,286],[]),([2,3,41,123,286],[]),([2,3,41,145,239],[]),([2,3,41,145,286],[124]),([2,3,145,199,286],[]),([2,3,123,125,286],[]),([2,3,125,145,239],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_3 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_3 = true := by decide +kernel
def h26Block4_4 : List NodeSpec := nodesWithIdentity [([2,3,17,160,286],[]),([2,3,43,160,286],[]),([2,3,6,161,286],[]),([2,3,6,160,239],[]),([2,3,17,132,145],[]),([2,3,43,132,145],[]),([2,3,6,145,258],[]),([2,3,6,123,132],[]),([2,3,145,164,286],[]),([2,3,145,165,286],[]),([2,3,17,145,286],[124]),([2,3,6,166,286],[]),([2,3,6,145,169],[]),([1,17,87,111,286],[33]),([1,3,22,111,286],[124]),([1,14,41,87,286],[88]),([1,3,41,90,286],[11]),([1,2,14,22,286],[124]),([1,2,17,90,286],[11]),([1,3,111,254,286],[]),([1,3,41,122,286],[]),([1,3,41,111,239],[]),([1,3,41,111,286],[124]),([1,3,111,165,286],[124]),([1,2,43,122,286],[]),([2,3,6,190,286],[0]),([3,41,111,145,286],[]),([2,3,41,286,308],[124]),([1,3,41,286,307],[124]),([1,2,16,254,286],[]),([1,2,41,286,303],[]),([1,3,125,130,286],[]),([1,2,14,199,286],[124]),([2,3,6,132,167],[]),([1,2,14,17,132],[]),([2,3,6,271,286],[0]),([1,2,17,130,286],[]),([1,2,14,164,286],[]),([1,2,14,17,286],[124]),([2,3,6,162,239],[]),([0,12,14,45,87],[22]),([0,6,14,33,87],[]),([0,4,12,26,87],[10]),([0,4,17,33,87],[5]),([0,4,17,38,87],[]),([0,4,12,39,87],[]),([0,4,12,17,90],[11]),([0,4,12,17,94],[]),([0,4,12,17,87],[10]),([0,3,12,45,90],[11]),([0,4,12,72,87],[10]),([0,3,12,47,94],[]),([3,4,6,12,333],[1]),([0,12,14,17,111],[33]),([0,6,14,55,111],[]),([0,3,12,26,111],[10]),([0,4,12,43,122],[]),([0,3,12,75,111],[10]),([0,3,45,55,111],[7]),([0,3,45,59,111],[]),([3,4,6,12,341],[1]),([0,3,12,45,122],[]),([0,3,12,60,111],[]),([0,3,12,45,111],[10]),([0,2,14,17,33],[5]),([0,2,14,45,55],[7]),([0,45,85,87,111],[22]),([0,6,87,88,111],[]),([0,4,24,85,87],[81]),([0,4,85,87,247],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_4 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_4 = true := by decide +kernel
def h26Block4_5 : List NodeSpec := nodesWithIdentity [([0,4,41,87,88],[12]),([0,4,41,87,89],[]),([0,4,41,85,90],[11]),([0,4,41,85,94],[]),([0,4,41,85,87],[81]),([0,2,45,85,90],[11]),([0,4,85,87,135],[81]),([0,2,47,85,94],[]),([2,4,6,85,333],[1]),([0,14,41,85,111],[88]),([0,3,41,88,111],[12]),([0,2,14,24,85],[81]),([2,4,41,85,361],[81]),([0,4,41,85,263],[81]),([0,2,15,85,247],[]),([0,2,41,85,264],[]),([0,4,85,125,130],[]),([0,2,14,85,210],[81]),([2,4,6,127,245],[]),([0,2,14,45,127],[]),([2,4,6,85,362],[1]),([0,2,45,85,130],[]),([0,2,14,85,131],[]),([0,2,14,45,85],[81]),([0,17,87,111,145],[33]),([0,3,22,111,145],[124]),([0,14,41,87,145],[88]),([0,3,41,90,145],[11]),([0,2,14,22,145],[124]),([0,2,17,90,145],[11]),([0,3,111,145,254],[]),([0,3,41,122,145],[]),([0,3,41,111,123],[]),([0,3,41,111,145],[124]),([0,3,111,145,165],[124]),([0,2,43,122,145],[]),([2,3,6,145,341],[1]),([2,3,41,145,373],[124]),([0,3,41,145,307],[124]),([0,2,16,145,254],[]),([0,2,41,145,303],[]),([0,3,125,130,145],[]),([0,2,14,145,199],[124]),([2,3,6,160,300],[]),([0,2,14,17,160],[]),([2,3,6,145,362],[1]),([0,2,17,130,145],[]),([0,2,14,145,164],[]),([0,2,14,17,145],[124]),([2,3,6,123,298],[]),([0,1,2,3,99],[]),([0,1,26,87,111],[10]),([0,1,14,22,111],[124]),([0,1,14,24,87],[81]),([1,4,41,87,361],[81]),([0,4,41,87,266],[81]),([0,1,15,87,247],[]),([0,1,41,87,264],[]),([1,4,41,87,385],[10,81]),([0,4,41,87,386],[10,81]),([1,2,3,4,345],[]),([0,2,3,4,197],[]),([0,1,3,4,195],[]),([0,1,2,4,156],[]),([2,3,4,5,66],[]),([1,2,3,4,391],[]),([0,1,2,4,392],[]),([0,1,2,254,304],[]),([1,2,3,304,340],[]),([0,2,3,189,304],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_5 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_5 = true := by decide +kernel
def h26Block4_6 : List NodeSpec := nodesWithIdentity [([0,1,3,164,304],[]),([2,3,5,6,99],[]),([0,1,86,87,99],[]),([1,3,41,111,373],[124]),([0,3,41,111,308],[124]),([0,1,16,111,254],[]),([0,1,41,111,303],[]),([1,3,41,111,403],[10,124]),([0,3,41,111,404],[10,124]),([1,2,3,4,407],[]),([0,1,2,3,408],[]),([1,2,4,265,326],[]),([0,2,4,176,265],[]),([0,1,4,131,265],[]),([0,1,2,247,265],[]),([2,4,5,6,156],[]),([0,1,110,111,156],[]),([1,2,14,41,413],[]),([1,2,4,254,413],[]),([1,2,3,247,413],[]),([0,2,14,41,415],[]),([0,2,4,254,415],[]),([0,2,3,247,415],[]),([0,1,14,41,252],[]),([0,1,4,252,254],[]),([0,1,3,247,252],[]),([0,1,2,14,414],[88]),([0,1,2,13,255],[]),([0,1,2,22,264],[88]),([0,1,2,4,417],[]),([0,1,2,24,303],[88]),([0,1,2,3,420],[]),([1,2,3,4,431],[]),([1,3,4,194,327],[]),([0,2,3,4,432],[]),([0,3,4,177,194],[]),([0,1,4,60,194],[]),([0,1,3,39,194],[]),([3,4,6,26,40],[12]),([3,4,5,6,195],[]),([2,4,6,26,248],[12]),([2,3,6,26,302],[12]),([2,3,4,6,434],[]),([4,12,18,85,220],[4]),([4,12,32,85,220],[12]),([4,10,33,85,220],[5]),([4,10,38,85,220],[5]),([4,10,12,88,220],[12]),([4,10,12,89,220],[12]),([4,10,12,85,224],[13]),([4,10,12,85,225],[5]),([10,12,14,145,220],[]),([4,10,55,145,220],[]),([3,12,18,145,220],[]),([3,10,12,145,224],[13]),([1,12,14,18,220],[]),([1,10,14,33,220],[5]),([1,4,10,19,220],[0]),([1,4,18,55,220],[7]),([1,4,32,55,220],[]),([1,4,10,56,220],[]),([1,4,10,55,224],[7]),([1,4,10,55,225],[]),([1,4,10,55,220],[0]),([1,3,10,33,224],[5]),([1,4,10,71,220],[0]),([1,3,10,38,225],[]),([3,4,10,12,180],[10]),([10,85,111,145,220],[]),([2,18,85,145,220],[4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_6 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_6 = true := by decide +kernel
def h26Block4_7 : List NodeSpec := nodesWithIdentity [([2,10,85,145,224],[]),([1,10,88,111,220],[12]),([1,10,85,111,224],[]),([1,2,18,88,220],[12]),([2,4,85,179,220],[81]),([1,2,32,89,220],[]),([1,4,10,138,220],[0]),([1,18,87,145,220],[]),([1,10,90,145,220],[]),([1,10,87,145,224],[]),([1,4,90,171,220],[]),([1,4,94,171,220],[]),([1,4,87,215,220],[]),([1,4,87,171,224],[]),([1,4,87,171,225],[]),([1,14,111,171,220],[12]),([1,3,111,171,224],[]),([2,4,171,174,220],[]),([1,2,14,215,220],[81]),([1,4,18,87,178],[]),([1,4,32,87,178],[]),([1,4,10,90,178],[]),([1,4,10,94,178],[]),([1,4,10,87,281],[]),([3,4,10,178,186],[]),([1,10,14,111,178],[5]),([1,3,10,111,281],[10]),([1,4,10,178,185],[]),([1,2,14,18,178],[]),([1,4,18,172,220],[]),([1,4,32,172,220],[]),([1,4,10,173,220],[]),([1,4,10,172,224],[]),([1,4,10,172,225],[]),([1,4,87,176,220],[]),([1,4,87,179,220],[]),([1,4,18,87,220],[81]),([1,4,10,181,220],[]),([1,4,10,182,220],[]),([1,4,10,90,220],[0]),([1,4,10,87,177],[]),([1,4,10,87,180],[]),([1,4,10,87,224],[10]),([1,10,14,186,220],[5]),([1,4,10,187,220],[0]),([1,3,10,186,224],[]),([1,10,111,174,220],[12]),([1,3,10,111,177],[]),([1,3,10,111,224],[10]),([1,4,10,220,276],[0]),([1,2,18,174,220],[]),([1,2,14,176,220],[]),([1,2,14,18,220],[81]),([3,4,10,83,177],[]),([10,12,14,85,286],[]),([4,12,44,85,286],[]),([3,10,33,85,286],[]),([3,10,12,88,286],[12]),([3,12,44,145,286],[6]),([3,12,54,145,286],[12]),([3,10,55,145,286],[7]),([3,10,59,145,286],[7]),([3,10,12,123,286],[12]),([3,10,12,145,239],[7]),([1,12,14,44,286],[]),([1,10,14,55,286],[7]),([1,3,10,19,286],[0]),([1,3,33,44,286],[5]),([1,3,33,54,286],[]),([1,4,10,59,239],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_7 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_7 = true := by decide +kernel
def h26Block4_8 : List NodeSpec := nodesWithIdentity [([1,3,10,78,286],[0]),([3,4,10,12,193],[10]),([1,3,10,33,239],[]),([1,3,10,62,286],[]),([1,3,10,33,286],[0]),([10,85,87,145,286],[]),([2,44,85,145,286],[6]),([1,10,87,88,286],[12]),([1,10,85,90,286],[]),([1,44,85,111,286],[]),([1,2,44,88,286],[12]),([2,3,145,192,286],[124]),([1,2,54,123,286],[]),([1,3,10,166,286],[0]),([1,14,87,171,286],[12]),([1,3,90,171,286],[]),([1,3,122,171,286],[]),([1,3,111,204,286],[]),([1,3,111,171,239],[]),([2,3,171,174,286],[]),([1,2,14,204,286],[124]),([3,4,10,172,175],[]),([1,10,14,87,175],[7]),([1,4,10,87,280],[10]),([1,3,10,90,175],[]),([1,3,10,175,191],[]),([1,3,44,111,175],[]),([1,3,54,111,175],[]),([1,3,10,122,175],[]),([1,3,10,111,280],[]),([1,2,14,44,175],[]),([1,10,14,172,286],[7]),([1,3,10,173,286],[0]),([1,10,87,174,286],[12]),([1,3,10,181,286],[]),([1,3,10,90,286],[0]),([1,3,44,186,286],[]),([1,3,54,186,286],[]),([1,3,10,187,286],[]),([1,3,10,186,239],[]),([1,3,111,189,286],[]),([1,3,111,192,286],[]),([1,3,44,111,286],[124]),([1,3,10,190,286],[]),([1,3,10,111,193],[]),([1,3,10,276,286],[0]),([1,2,44,174,286],[]),([1,2,14,189,286],[]),([1,2,14,44,286],[124]),([1,3,10,188,239],[]),([0,12,14,18,85],[4]),([0,10,14,33,85],[]),([0,4,12,28,85],[1]),([0,4,33,44,85],[5]),([0,4,38,44,85],[]),([0,4,12,51,85],[]),([0,4,12,44,88],[12]),([0,4,12,44,89],[]),([0,4,12,44,85],[1]),([0,3,12,18,88],[12]),([0,4,12,70,85],[1]),([0,3,12,32,89],[]),([3,4,10,12,330],[10]),([0,12,14,44,145],[6]),([0,10,14,55,145],[]),([0,3,12,28,145],[1]),([0,4,12,54,123],[]),([0,3,12,77,145],[1]),([0,3,18,55,145],[7]),([0,3,18,59,145],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_8 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_8 = true := by decide +kernel
def h26Block4_9 : List NodeSpec := nodesWithIdentity [([3,4,10,12,343],[10]),([0,3,12,18,123],[]),([0,3,12,61,145],[]),([0,3,12,18,145],[1]),([0,1,14,33,44],[5]),([0,1,14,18,55],[7]),([0,18,85,87,145],[4]),([0,10,85,90,145],[]),([0,44,85,111,145],[6]),([0,2,28,85,145],[1]),([2,4,41,85,457],[1,81]),([0,4,41,85,358],[1,81]),([0,1,18,87,88],[12]),([0,4,85,87,179],[81]),([0,1,32,87,89],[]),([1,4,10,87,330],[10]),([0,1,44,88,111],[12]),([1,3,4,9,63],[]),([1,3,9,10,99],[]),([0,2,84,85,99],[]),([2,3,41,145,465],[1,124]),([0,3,41,145,372],[1,124]),([0,3,111,145,192],[124]),([0,1,54,111,123],[]),([1,3,10,111,343],[10]),([3,4,10,52,123],[]),([1,4,10,123,227],[0]),([1,3,10,123,294],[]),([1,3,4,10,467],[]),([1,4,9,10,156],[]),([0,2,144,145,156],[]),([0,4,87,171,174],[]),([0,1,14,87,215],[81]),([0,3,111,171,174],[]),([0,1,14,111,204],[124]),([1,4,10,172,245],[]),([0,1,14,18,172],[]),([1,4,10,87,423],[10]),([0,1,18,87,174],[]),([0,1,14,87,176],[]),([0,1,14,18,87],[81]),([1,3,10,186,300],[]),([0,1,14,44,186],[]),([1,3,10,111,423],[10]),([0,1,44,111,174],[]),([0,1,14,111,189],[]),([0,1,14,44,111],[124]),([1,2,3,4,477],[]),([0,1,3,4,478],[]),([2,3,4,196,332],[]),([0,3,4,133,196],[]),([0,2,4,61,196],[]),([0,2,3,51,196],[]),([3,4,10,28,52],[11]),([3,4,9,10,197],[]),([1,4,10,28,227],[11]),([1,3,10,28,294],[11]),([1,3,4,10,480],[]),([12,85,111,220,286],[]),([2,33,85,220,286],[5]),([2,12,88,220,286],[]),([12,87,145,220,286],[]),([2,55,145,220,286],[7]),([1,33,87,220,286],[5]),([1,12,90,220,286],[]),([1,55,111,220,286],[7]),([1,2,19,220,286],[0]),([2,127,145,220,286],[7]),([2,85,160,220,286],[5]),([2,85,134,145,286],[5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_9 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_9 = true := by decide +kernel
def h26Block4_10 : List NodeSpec := nodesWithIdentity [([2,85,132,145,220],[7]),([1,4,127,132,220],[]),([1,2,128,220,286],[0]),([1,2,88,134,286],[]),([2,4,85,208,220],[81]),([1,2,88,132,220],[]),([1,2,137,220,286],[]),([1,2,88,220,286],[0]),([1,3,134,160,286],[]),([1,2,161,220,286],[0]),([2,3,145,198,286],[124]),([1,87,111,178,286],[5]),([1,2,90,178,286],[]),([2,3,178,186,286],[]),([1,3,111,203,286],[124]),([1,2,178,286,311],[]),([1,2,14,203,286],[]),([1,2,14,132,178],[]),([1,2,130,178,286],[]),([2,4,172,175,220],[]),([1,87,111,175,220],[7]),([1,4,87,213,220],[81]),([1,2,90,175,220],[]),([1,2,175,220,272],[]),([1,2,14,213,220],[]),([1,2,14,134,175],[]),([1,2,130,175,220],[]),([1,111,172,220,286],[7]),([1,2,173,220,286],[0]),([1,87,186,220,286],[5]),([1,2,181,220,286],[]),([1,2,90,220,286],[0]),([1,2,187,220,286],[0]),([1,2,134,286,315],[]),([1,2,14,198,286],[]),([1,2,134,174,286],[]),([1,2,132,220,277],[]),([1,2,14,208,220],[]),([1,2,132,174,220],[]),([1,2,220,276,286],[]),([1,2,220,271,286],[]),([2,4,41,220,437],[0,81]),([1,4,41,220,259],[0,81]),([0,12,88,111,220],[]),([0,12,85,111,224],[13]),([0,2,33,85,224],[5]),([2,4,85,220,329],[81]),([0,2,38,85,225],[]),([0,4,12,85,136],[1]),([0,12,90,145,220],[]),([0,12,87,145,224],[13]),([0,55,111,145,220],[]),([0,2,55,145,224],[7]),([0,1,33,87,224],[5]),([1,4,87,220,329],[81]),([0,1,38,87,225],[]),([0,4,12,87,180],[10]),([0,1,55,111,224],[7]),([0,3,4,11,65],[]),([0,3,11,12,99],[]),([2,4,22,104,220],[7]),([1,4,22,95,220],[7]),([1,2,99,219,220],[]),([1,2,22,220,290],[7]),([1,2,4,220,496],[]),([0,2,127,145,224],[]),([2,4,85,220,352],[81]),([0,4,85,134,160],[]),([0,2,85,160,224],[]),([0,2,85,145,240],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_10 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_10 = true := by decide +kernel
def h26Block4_11 : List NodeSpec := nodesWithIdentity [([0,2,85,133,145],[]),([0,2,85,145,224],[1]),([2,4,127,184,220],[]),([2,4,85,134,335],[]),([0,4,82,85,133],[]),([2,4,104,160,220],[]),([1,4,95,160,220],[0]),([1,2,160,220,290],[]),([1,2,4,220,498],[]),([1,2,14,220,352],[81]),([0,1,14,134,160],[]),([2,3,134,145,287],[]),([0,3,134,145,235],[1]),([0,2,114,134,145],[]),([0,2,3,145,499],[]),([0,2,14,145,198],[124]),([0,3,82,133,145],[]),([0,4,87,178,186],[]),([0,1,87,111,281],[10]),([1,4,87,178,454],[]),([1,3,111,178,410],[]),([0,3,111,178,411],[10]),([0,1,111,149,178],[]),([0,1,3,111,500],[]),([0,2,14,178,186],[]),([0,1,14,111,203],[124]),([1,2,14,178,465],[]),([1,4,140,172,220],[]),([0,1,111,172,224],[]),([1,4,87,220,397],[81]),([0,1,87,186,224],[]),([0,1,87,111,177],[]),([0,1,87,111,224],[10]),([0,4,83,87,177],[]),([2,4,104,186,220],[0]),([1,4,95,186,220],[]),([1,2,186,220,290],[]),([1,2,4,220,502],[]),([1,2,14,220,397],[81]),([0,3,83,111,177],[]),([1,2,14,134,403],[]),([0,3,4,26,67],[13]),([0,2,3,4,503],[]),([2,3,4,57,177],[]),([0,2,4,97,177],[]),([0,2,3,155,177],[]),([0,3,4,28,64],[13]),([0,1,3,4,504],[]),([1,3,4,57,133],[]),([0,1,4,97,133],[]),([0,1,3,133,155],[]),([2,4,104,177,220],[]),([1,4,95,177,220],[]),([1,2,177,220,290],[]),([1,2,4,220,505],[]),([2,4,104,133,220],[]),([1,4,95,133,220],[]),([1,2,133,220,290],[]),([1,2,4,220,506],[]),([2,3,41,286,446],[0,124]),([1,3,41,286,305],[0,124]),([0,33,85,87,286],[]),([0,12,87,88,286],[]),([0,12,85,90,286],[]),([2,3,145,286,342],[124]),([0,2,59,145,239],[]),([0,3,12,145,169],[1]),([1,3,111,286,342],[124]),([0,1,59,111,239],[]),([0,3,12,111,193],[10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_11 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_11 = true := by decide +kernel
def h26Block4_12 : List NodeSpec := nodesWithIdentity [([3,4,12,57,239],[]),([0,4,12,97,239],[1]),([0,3,12,155,239],[]),([0,3,4,12,508],[]),([0,4,11,12,156],[]),([2,3,24,146,286],[5]),([1,3,24,113,286],[5]),([1,2,156,285,286],[]),([1,2,24,236,286],[5]),([1,2,3,286,511],[]),([2,3,145,286,346],[124]),([0,3,127,132,145],[]),([0,2,85,145,258],[1]),([2,3,127,146,286],[]),([1,3,113,127,286],[0]),([1,2,127,236,286],[]),([1,2,3,286,513],[]),([1,2,14,286,346],[124]),([0,1,14,127,132],[]),([2,4,85,132,231],[]),([0,4,85,132,226],[1]),([0,2,85,132,150],[]),([0,2,4,85,514],[]),([0,2,14,85,208],[81]),([2,3,160,183,286],[]),([2,3,132,145,334],[]),([2,3,123,261,286],[]),([2,3,145,239,360],[]),([1,4,87,175,394],[]),([0,4,87,175,395],[10]),([0,1,87,116,175],[]),([0,1,4,87,515],[]),([0,3,111,172,175],[]),([0,2,14,172,175],[]),([0,1,87,111,280],[10]),([0,1,14,87,213],[81]),([1,3,111,175,453],[]),([1,2,14,175,457],[]),([2,3,146,172,286],[0]),([1,3,113,172,286],[]),([1,2,172,236,286],[]),([1,2,3,286,517],[]),([1,3,111,286,379],[124]),([1,2,14,286,379],[124]),([1,3,139,186,286],[]),([1,3,111,239,458],[]),([1,2,14,132,385],[]),([2,3,146,177,286],[]),([1,3,113,177,286],[]),([1,2,177,236,286],[]),([1,2,3,286,518],[]),([2,3,133,146,286],[]),([1,3,113,133,286],[]),([1,2,133,236,286],[]),([1,2,3,286,519],[]),([0,4,87,88,320],[]),([0,4,87,89,320],[]),([0,4,85,90,320],[]),([0,4,85,94,320],[]),([0,4,85,87,355],[]),([0,14,85,111,320],[13]),([0,3,88,111,320],[]),([2,4,85,320,323],[]),([0,2,14,85,355],[81]),([0,14,87,145,320],[13]),([0,3,90,145,320],[]),([0,3,122,145,320],[]),([0,3,111,123,320],[]),([0,3,111,145,348],[]),([2,3,145,320,323],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_12 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_12 = true := by decide +kernel
def h26Block4_13 : List NodeSpec := nodesWithIdentity [([0,2,14,145,348],[124]),([1,4,87,320,323],[]),([0,1,14,87,355],[81]),([1,3,111,320,323],[]),([0,1,14,111,348],[124]),([0,4,33,87,328],[]),([0,4,38,87,328],[]),([0,4,12,90,328],[]),([0,4,12,94,328],[]),([0,4,12,87,369],[]),([3,4,12,328,336],[]),([0,12,14,111,328],[4]),([0,3,12,111,369],[10]),([0,4,12,185,328],[]),([0,2,14,33,328],[]),([0,4,33,85,321],[]),([0,4,38,85,321],[]),([0,4,12,88,321],[]),([0,4,12,89,321],[]),([0,4,12,85,322],[]),([0,4,85,87,326],[]),([0,4,85,87,329],[]),([0,4,33,85,87],[81]),([0,4,12,87,327],[]),([0,4,12,87,330],[]),([0,4,12,87,88],[10]),([0,4,12,85,332],[]),([0,4,12,85,333],[]),([0,4,12,85,90],[1]),([0,12,14,85,336],[4]),([0,4,12,85,337],[1]),([0,3,12,88,336],[]),([0,12,85,111,323],[13]),([0,3,12,111,327],[]),([0,3,12,88,111],[10]),([0,4,12,85,365],[1]),([0,2,33,85,323],[]),([0,2,14,85,326],[]),([0,2,14,33,85],[81]),([3,4,12,218,327],[]),([3,4,12,321,324],[]),([0,12,14,87,324],[6]),([0,4,12,87,368],[10]),([0,3,12,90,324],[]),([0,3,12,191,324],[]),([0,3,55,111,324],[]),([0,3,59,111,324],[]),([0,3,12,122,324],[]),([0,3,12,111,368],[]),([0,2,14,55,324],[]),([0,12,14,145,321],[6]),([0,3,12,145,322],[1]),([0,12,87,145,323],[13]),([0,3,12,145,332],[]),([0,3,12,90,145],[1]),([0,3,55,145,336],[]),([0,3,59,145,336],[]),([0,3,12,123,336],[]),([0,3,12,145,337],[]),([0,3,111,145,340],[]),([0,3,111,145,342],[]),([0,3,55,111,145],[124]),([0,3,12,145,341],[]),([0,3,12,111,343],[]),([0,3,12,145,365],[1]),([0,2,55,145,323],[]),([0,2,14,145,340],[]),([0,2,14,55,145],[124]),([0,3,12,123,338],[]),([0,4,12,141,321],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_13 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_13 = true := by decide +kernel
def h26Block4_14 : List NodeSpec := nodesWithIdentity [([0,1,14,33,321],[]),([0,4,12,87,424],[10]),([0,1,33,87,323],[]),([0,1,14,87,326],[]),([0,1,14,33,87],[81]),([0,3,12,167,336],[]),([0,1,14,55,336],[]),([0,3,12,111,424],[10]),([0,1,55,111,323],[]),([0,1,14,111,340],[]),([0,1,14,55,111],[124]),([2,3,4,181,344],[]),([1,3,4,137,344],[]),([1,2,4,62,344],[]),([1,2,3,56,344],[]),([1,2,3,22,299],[7]),([1,2,3,4,525],[]),([1,2,4,24,241],[5]),([1,2,3,4,526],[]),([0,87,111,145,328],[4]),([0,2,90,145,328],[]),([2,3,145,328,336],[]),([0,3,111,145,347],[124]),([0,2,145,311,328],[]),([0,2,14,160,328],[]),([0,2,14,145,347],[]),([0,2,130,145,328],[]),([1,4,87,328,336],[]),([0,1,87,111,369],[10]),([0,4,87,328,436],[]),([1,3,111,328,410],[10]),([0,3,111,328,411],[]),([0,1,111,149,328],[]),([0,1,3,111,528],[]),([1,2,14,328,336],[]),([0,1,14,111,347],[124]),([0,2,14,328,446],[]),([2,4,85,321,324],[]),([0,85,87,111,324],[6]),([0,4,85,87,353],[81]),([0,2,85,90,324],[]),([0,2,85,272,324],[]),([0,2,14,127,324],[]),([0,2,14,85,353],[]),([0,2,85,130,324],[]),([0,85,111,145,321],[6]),([0,2,85,145,322],[1]),([0,85,87,145,336],[4]),([0,2,85,145,332],[]),([0,2,85,90,145],[1]),([0,2,85,145,337],[1]),([0,2,127,145,376],[]),([0,2,14,145,346],[]),([0,2,127,145,323],[]),([0,2,85,160,366],[]),([0,2,14,85,352],[]),([0,2,85,160,323],[]),([0,2,85,145,365],[]),([0,2,85,145,362],[]),([0,4,85,244,321],[]),([0,1,88,111,321],[]),([0,4,85,87,398],[81]),([0,1,87,88,336],[]),([0,1,87,111,327],[]),([0,1,87,88,111],[10]),([1,4,87,218,327],[]),([2,4,85,231,336],[1]),([0,4,85,226,336],[]),([0,2,85,150,336],[]),([0,2,4,85,532],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_14 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_14 = true := by decide +kernel
def h26Block4_15 : List NodeSpec := nodesWithIdentity [([0,2,14,85,398],[81]),([1,3,111,218,327],[]),([0,2,14,127,404],[]),([1,3,4,26,69],[12]),([1,2,3,4,533],[]),([2,3,4,52,327],[]),([1,2,4,227,327],[]),([1,2,3,294,327],[]),([2,4,85,231,327],[]),([0,4,85,226,327],[]),([0,2,85,150,327],[]),([0,2,4,85,534],[]),([1,4,87,324,394],[10]),([0,4,87,324,395],[]),([0,1,87,116,324],[]),([0,1,4,87,535],[]),([1,3,111,321,324],[]),([1,2,14,321,324],[]),([0,1,87,111,368],[10]),([0,1,14,87,353],[81]),([0,3,111,324,435],[]),([0,2,14,324,437],[]),([2,3,145,287,321],[1]),([0,3,145,235,321],[]),([0,2,114,145,321],[]),([0,2,3,145,536],[]),([0,3,111,145,380],[124]),([0,2,14,145,380],[124]),([0,3,145,243,336],[]),([0,3,111,123,489],[]),([0,2,14,160,386],[]),([2,3,145,287,327],[]),([0,3,145,235,327],[]),([0,2,114,145,327],[]),([0,2,3,145,537],[]),([0,1,111,315,321],[]),([0,1,14,305,321],[]),([0,1,14,111,380],[]),([0,1,14,186,321],[]),([0,1,111,174,321],[]),([0,1,111,172,376],[]),([0,1,14,172,372],[]),([0,1,14,111,379],[]),([0,1,14,172,336],[]),([0,1,111,172,323],[]),([0,1,87,277,336],[]),([0,1,14,87,398],[]),([0,1,87,174,336],[]),([0,1,87,186,366],[]),([0,1,14,87,397],[]),([0,1,87,186,323],[]),([0,1,87,111,424],[]),([0,1,87,111,423],[]),([2,3,4,28,68],[11]),([1,2,3,4,542],[]),([0,1,14,259,336],[]),([0,1,14,186,358],[]),([1,2,14,177,413],[]),([0,2,14,177,415],[]),([0,1,14,177,252],[]),([0,1,2,14,543],[]),([1,2,14,133,413],[]),([0,2,14,133,415],[]),([0,1,14,133,252],[]),([0,1,2,14,544],[]),([1,2,14,327,413],[]),([0,2,14,327,415],[]),([0,1,14,252,327],[]),([0,1,2,14,545],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test4_15 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Block4_15 = true := by decide +kernel
def h26Nodes4 : List NodeSpec := h26Block4_0 ++ h26Block4_1 ++ h26Block4_2 ++ h26Block4_3 ++ h26Block4_4 ++ h26Block4_5 ++ h26Block4_6 ++ h26Block4_7 ++ h26Block4_8 ++ h26Block4_9 ++ h26Block4_10 ++ h26Block4_11 ++ h26Block4_12 ++ h26Block4_13 ++ h26Block4_14 ++ h26Block4_15
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Check4 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket3 4 h26Nodes4 = true := by
  unfold h26Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h26Test4_0,h26Test4_1⟩,h26Test4_2⟩,h26Test4_3⟩,h26Test4_4⟩,h26Test4_5⟩,h26Test4_6⟩,h26Test4_7⟩,h26Test4_8⟩,h26Test4_9⟩,h26Test4_10⟩,h26Test4_11⟩,h26Test4_12⟩,h26Test4_13⟩,h26Test4_14⟩,h26Test4_15⟩
def h26Bucket4 : BT (List (List Nat)) := buildBucketsBT h26W h26Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G 4 xs.toFinset) h26Bucket4 := buildBucketsBT_sound (by decide) h26Pairs h26WOk h26PoolsOk h26AutosOk h26Bucket3Ok h26Check4
def h26Block5_0 : List NodeSpec := nodesWithIdentity [([3,4,6,10,12,14],[3,8,9,11,12,13]),([3,4,10,12,17],[4,5,10,11,15,16]),([3,4,6,10,12,17],[4,5,11,15,17,18,19]),([3,4,10,12,43],[11,12,13]),([3,4,6,12,44],[1,5,12,20,21,22]),([3,4,6,10,12,44],[2,5,12,20,21,22,23]),([3,4,6,12,54],[11,12,13]),([3,4,6,10,55],[0,3,4,13,22,24]),([3,4,6,10,12,55],[3,4,13,22,24,25,26]),([3,4,6,10,59],[11,12,13]),([3,4,10,12,45],[6,7,10,11,27,28]),([3,4,6,10,12,45],[6,7,11,19,27,29,30]),([3,4,10,12,47],[11,12,13]),([3,4,6,12,18],[1,7,12,31,32,33]),([3,4,6,10,12,18],[2,7,12,31,32,33,34]),([3,4,6,12,32],[11,12,13]),([3,4,6,10,33],[0,6,13,14,33,35]),([3,4,6,10,12,33],[6,13,14,26,33,35,36]),([3,4,6,10,38],[11,12,13]),([4,6,10,85,87],[4,11,12,22]),([3,4,6,10,85,111],[]),([2,3,4,6,10,55],[0]),([3,4,6,10,55,85],[4,13,39]),([2,3,4,6,10,127],[0]),([2,4,6,10,14,85],[]),([2,4,6,44,85],[1,5,12,21,22,40]),([2,3,4,6,44,85],[1]),([2,4,6,10,44,85],[2,5,12]),([2,3,4,6,54,85],[1]),([2,3,4,10,45,85],[]),([2,3,4,10,47,85],[]),([2,3,4,6,18,85],[4]),([2,3,4,6,32,85],[12]),([2,3,4,6,10,88],[12]),([2,3,4,6,10,89],[12]),([3,4,6,10,87,145],[]),([3,6,10,111,145],[6,11,12,33]),([2,3,4,6,10,33],[0]),([3,4,6,10,33,145],[6,13,43]),([2,3,4,6,10,160],[0]),([2,3,6,10,14,145],[]),([2,3,4,10,17,145],[]),([2,3,4,10,43,145],[]),([2,3,4,6,44,145],[6]),([2,3,4,6,54,145],[12]),([2,3,4,6,10,123],[12]),([2,3,6,18,145],[1,7,12,32,33,44]),([2,3,4,6,18,145],[1]),([2,3,6,10,18,145],[2,7,12]),([2,3,4,6,32,145],[1]),([1,3,4,6,10,55],[0]),([3,4,6,10,55,87],[13,22,46]),([1,3,4,6,10,172],[0]),([1,4,6,10,14,87],[]),([1,4,10,17,87],[4,5,10,11,16,47]),([1,3,4,10,17,87],[10]),([1,4,6,10,17,87],[5,11,19]),([1,3,4,10,43,87],[10]),([1,3,4,10,45,87],[22]),([1,3,4,10,47,87],[11]),([1,3,4,6,18,87],[]),([1,3,4,6,32,87],[]),([1,3,4,6,10,90],[11]),([1,3,4,6,10,94],[11]),([1,3,4,6,10,33],[0]),([3,4,6,10,33,111],[13,33,49]),([1,3,4,6,10,186],[0]),([1,3,6,10,14,111],[]),([1,3,4,10,17,111],[33]),([1,3,4,10,43,111],[11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_0 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_0 = true := by decide +kernel
def h26Block5_1 : List NodeSpec := nodesWithIdentity [([1,3,4,6,44,111],[]),([1,3,4,6,54,111],[]),([1,3,4,6,10,122],[11]),([1,3,10,45,111],[6,7,10,11,28,50]),([1,3,4,10,45,111],[10]),([1,3,6,10,45,111],[7,11,19]),([1,3,4,10,47,111],[10]),([1,2,4,10,14,17],[]),([1,2,4,6,14,44],[]),([1,2,3,10,14,45],[]),([1,2,3,6,14,18],[]),([1,2,3,4,10,26],[10]),([1,2,3,4,6,28],[1]),([1,3,4,10,17,164],[5,10,11]),([1,2,3,4,17,18],[4]),([1,2,3,4,17,32],[]),([1,2,3,4,10,39],[10,54]),([1,3,4,6,10,164],[5,10]),([1,2,3,4,10,17],[10,18]),([1,2,3,4,18,43],[]),([1,2,3,4,32,43],[]),([1,2,3,4,10,75],[10]),([2,3,4,6,44,189],[1,5,12]),([1,2,3,4,44,45],[6]),([1,2,3,4,44,47],[]),([1,2,3,4,6,51],[1,59]),([2,3,4,6,10,189],[1,5]),([1,2,3,4,6,44],[1,23]),([1,2,3,4,45,54],[]),([1,2,3,4,47,54],[]),([1,2,3,4,6,77],[1]),([1,3,4,10,45,131],[7,10,11]),([1,2,3,4,10,60],[10,66]),([1,3,4,6,10,131],[7,10]),([1,2,3,4,10,72],[10]),([1,2,3,4,10,45],[10,30]),([2,3,4,6,18,176],[1,7,12]),([1,2,3,4,6,61],[1,71]),([2,3,4,6,10,176],[1,7]),([1,2,3,4,6,70],[1]),([1,2,3,4,6,18],[1,34]),([4,6,12,87,220],[5,11,13,22]),([3,4,6,12,111,220],[]),([2,3,4,6,12,44],[1]),([3,4,6,12,44,220],[5,12,76]),([2,3,4,6,12,134],[1]),([2,4,6,12,14,220],[]),([2,4,6,55,220],[0,4,13,22,24,79]),([2,3,4,6,55,220],[0]),([2,4,6,12,55,220],[4,13,26]),([2,3,4,6,59,220],[0]),([2,3,4,12,45,220],[]),([2,3,4,12,47,220],[]),([2,3,4,6,33,220],[5]),([2,3,4,6,38,220],[5]),([2,3,4,6,12,224],[13]),([2,3,4,6,12,225],[5]),([2,4,6,85,111,220],[4,5,11,49,80,82]),([2,4,41,85,220],[11,12,13,81,84]),([2,4,6,41,85,220],[2,11,12,13,26,84,85]),([2,4,85,125,220],[4,5,11]),([2,4,6,55,85,220],[4,13,22,24,25,39,79]),([2,4,6,127,220],[4,11,12]),([2,4,6,44,85,220],[5,12,21,22,23,40,76]),([2,4,6,85,134],[5,11,13]),([2,4,45,85,220],[6,7,11,81,83,86]),([2,4,6,45,85,220],[6,7,11,29,30,83,85]),([2,4,47,85,220],[4,5,11]),([2,4,6,88,220],[0,4,6,83,87,88]),([2,4,6,85,88,220],[4,6,39,83,87,88,89])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_1 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_1 = true := by decide +kernel
def h26Block5_2 : List NodeSpec := nodesWithIdentity [([2,4,6,89,220],[4,5,11]),([2,4,6,85,224],[1,5,7,83,88,90]),([2,4,6,85,220,224],[5,7,76,83,88,90,91]),([2,4,6,85,225],[4,5,11]),([2,4,6,87,145,220],[]),([2,3,6,111,145,220],[]),([2,3,4,41,145,220],[]),([2,3,4,125,145,220],[]),([2,3,4,6,160,220],[5]),([2,3,4,6,134,145],[5]),([2,6,14,145,220],[5,6,11,88]),([2,3,4,6,88,220],[0]),([2,4,6,88,145,220],[4,6,43]),([2,3,4,6,123,220],[0]),([2,3,6,145,224],[1,5,7,88,90,94]),([2,3,4,6,145,224],[1]),([2,3,6,145,220,224],[5,7,76]),([2,3,4,6,145,225],[1]),([1,2,4,6,55,220],[0]),([2,4,6,55,87,220],[4,22,46]),([1,2,4,6,172,220],[0]),([1,4,6,87,111,220],[]),([1,4,41,87,220],[11,12,13,81,96]),([1,2,4,41,87,220],[81]),([1,4,6,41,87,220],[11,12,85]),([1,2,4,87,125,220],[81]),([1,2,4,45,87,220],[22]),([1,2,4,47,87,220],[11]),([1,2,4,6,90,220],[11]),([1,2,4,6,94,220],[11]),([1,2,4,6,87,224],[]),([1,2,4,6,87,225],[]),([1,3,4,41,111,220],[]),([1,2,6,14,111,220],[]),([1,2,3,45,111,220],[]),([1,2,3,6,111,224],[]),([1,2,3,4,24,220],[81]),([2,3,4,41,85,220],[81,84]),([1,3,4,41,87,220],[81,96]),([1,2,4,14,41,220],[88]),([1,2,4,15,41,220],[81]),([1,2,4,41,220,253],[11,12]),([1,2,4,41,220,254],[11,12,81]),([1,2,3,4,220,247],[81]),([1,2,3,4,41,224],[13]),([1,2,3,4,41,225],[]),([1,2,4,6,220,254],[12,81]),([1,2,3,4,41,220],[26,81]),([1,2,4,14,125,220],[11]),([1,2,3,4,210,220],[81]),([1,2,3,4,125,224],[]),([1,2,3,4,125,225],[]),([2,3,4,6,189,220],[1,12]),([1,2,4,6,85,134],[1]),([2,3,4,6,134,153],[1]),([1,2,4,6,14,134],[]),([1,2,3,4,45,134],[]),([1,2,3,4,47,134],[]),([1,2,3,4,6,240],[1]),([1,2,4,6,88,220],[0]),([2,4,6,14,88,220],[4,9,88]),([1,2,4,6,174,220],[0]),([1,2,4,6,130,220],[11]),([1,2,14,45,220],[6,7,11,81,86,106]),([1,2,4,14,45,220],[81]),([1,2,6,14,45,220],[7,11,85]),([1,2,4,14,47,220],[81]),([1,2,3,4,131,220],[81,108]),([1,2,4,45,60,220],[7,11,81]),([1,2,4,6,60,220],[7,81])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_2 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_2 = true := by decide +kernel
def h26Block5_3 : List NodeSpec := nodesWithIdentity [([1,2,3,4,135,220],[81]),([1,2,3,4,45,220],[30,81]),([2,3,4,6,177,224],[1,5,7]),([1,2,3,4,6,133],[1]),([2,3,4,6,177,220],[1,7]),([1,2,3,4,6,136],[1]),([1,2,3,4,6,224],[1,91]),([3,4,6,12,87,286],[]),([3,6,12,111,286],[7,11,13,33]),([2,3,4,6,12,18],[1]),([3,4,6,12,18,286],[7,12,116]),([2,3,4,6,12,132],[1]),([2,3,6,12,14,286],[]),([2,3,4,12,17,286],[]),([2,3,4,12,43,286],[]),([2,3,4,6,55,286],[7]),([2,3,4,6,59,286],[7]),([2,3,4,6,12,239],[7]),([2,3,6,33,286],[0,6,13,33,35,119]),([2,3,4,6,33,286],[0]),([2,3,6,12,33,286],[6,13,26]),([2,3,4,6,38,286],[0]),([2,4,6,85,87,286],[]),([2,3,6,85,111,286],[]),([2,3,4,41,85,286],[]),([2,3,4,85,125,286],[]),([2,3,4,6,127,286],[7]),([2,3,4,6,85,132],[7]),([2,6,14,85,286],[4,7,11,88]),([2,3,4,6,85,224],[1]),([2,4,6,85,224,286],[5,7,116]),([2,3,4,6,85,239],[1]),([2,3,6,88,286],[0,4,6,87,88,122]),([2,3,4,6,88,286],[0]),([2,3,6,85,88,286],[4,6,39]),([2,3,4,6,89,286],[0]),([2,3,6,87,145,286],[6,7,11,46,123,125]),([2,3,41,145,286],[11,12,13,124,127]),([2,3,6,41,145,286],[2,11,12,13,26,127,128]),([2,3,125,145,286],[6,7,11]),([2,3,6,33,145,286],[6,13,33,35,36,43,119]),([2,3,6,160,286],[6,11,12]),([2,3,6,18,145,286],[7,12,32,33,34,44,116]),([2,3,6,132,145],[7,11,13]),([2,3,17,145,286],[4,5,11,124,126,129]),([2,3,6,17,145,286],[4,5,11,17,18,126,128]),([2,3,43,145,286],[6,7,11]),([2,3,6,88,145,286],[4,6,43,87,88,89,122]),([2,3,6,123,286],[5,6,11]),([2,3,6,145,224,286],[5,7,88,90,91,94,116]),([2,3,6,145,239],[4,7,11]),([1,3,6,87,111,286],[]),([1,3,4,41,87,286],[]),([1,2,6,14,87,286],[]),([1,2,4,17,87,286],[]),([1,2,3,6,90,286],[11]),([1,2,3,4,22,286],[124]),([1,2,3,6,33,286],[0]),([2,3,6,33,111,286],[6,33,49]),([1,2,3,6,186,286],[0]),([1,3,41,111,286],[11,12,13,124,132]),([1,2,3,41,111,286],[124]),([1,3,6,41,111,286],[11,12,128]),([1,2,3,111,125,286],[124]),([1,2,3,17,111,286],[33]),([1,2,3,43,111,286],[11]),([1,2,3,6,122,286],[11]),([1,2,3,6,111,239],[]),([2,3,4,41,145,286],[124,127]),([1,3,4,41,111,286],[124,132])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_3 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_3 = true := by decide +kernel
def h26Block5_4 : List NodeSpec := nodesWithIdentity [([1,2,3,14,41,286],[88]),([1,2,3,16,41,286],[124]),([1,2,3,4,254,286],[124]),([1,2,3,4,41,239],[]),([1,2,3,41,246,286],[11,12]),([1,2,3,41,247,286],[11,12,124]),([1,2,3,6,247,286],[12,124]),([1,2,3,4,41,286],[26,124]),([1,2,3,14,125,286],[11]),([1,2,3,4,199,286],[124]),([1,2,3,4,125,239],[]),([2,3,4,6,176,286],[1,12]),([2,3,4,6,121,132],[1]),([1,2,3,6,132,145],[1]),([1,2,3,6,14,132],[]),([1,2,3,4,17,132],[]),([1,2,3,4,43,132],[]),([1,2,3,4,6,258],[1]),([1,2,3,6,88,286],[0]),([2,3,6,14,88,286],[6,9,88]),([1,2,3,6,174,286],[0]),([1,2,3,6,130,286],[11]),([1,2,14,17,286],[4,5,11,124,129,140]),([1,2,3,14,17,286],[124]),([1,2,6,14,17,286],[5,11,128]),([1,2,3,14,43,286],[124]),([1,2,3,4,164,286],[124,142]),([1,2,3,17,39,286],[5,11,124]),([1,2,3,6,39,286],[5,124]),([1,2,3,4,165,286],[124]),([1,2,3,4,17,286],[18,124]),([2,3,4,6,177,286],[1,5]),([2,3,4,6,82,239],[1]),([1,2,3,6,145,239],[1]),([1,2,3,4,6,169],[1]),([0,3,4,6,12,44],[1]),([3,4,6,12,44,87],[12,22,125]),([0,3,4,6,12,321],[1]),([0,4,6,12,14,87],[]),([0,4,12,17,87],[4,5,10,11,16,148]),([0,3,4,12,17,87],[10]),([0,4,6,12,17,87],[4,11,19]),([0,3,4,12,43,87],[10]),([0,3,4,12,45,87],[22]),([0,3,4,12,47,87],[11]),([0,3,4,6,33,87],[]),([0,3,4,6,38,87],[]),([0,3,4,6,12,90],[11]),([0,3,4,6,12,94],[11]),([0,3,4,6,12,18],[1]),([3,4,6,12,18,111],[12,33,82]),([0,3,4,6,12,336],[1]),([0,3,6,12,14,111],[]),([0,3,4,12,17,111],[33]),([0,3,4,12,43,111],[11]),([0,3,4,6,55,111],[]),([0,3,4,6,59,111],[]),([0,3,4,6,12,122],[11]),([0,3,12,45,111],[6,7,10,11,28,150]),([0,3,4,12,45,111],[10]),([0,3,6,12,45,111],[6,11,19]),([0,3,4,12,47,111],[10]),([0,2,4,12,14,17],[]),([0,2,4,6,14,55],[]),([0,2,3,12,14,45],[]),([0,2,3,6,14,33],[]),([0,2,3,4,12,26],[10]),([0,2,3,4,6,19],[0]),([0,3,4,12,17,164],[4,10,11]),([0,2,3,4,17,33],[5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_4 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_4 = true := by decide +kernel
def h26Block5_5 : List NodeSpec := nodesWithIdentity [([0,2,3,4,17,38],[]),([0,2,3,4,12,39],[10,54]),([0,3,4,6,12,164],[4,10]),([0,2,3,4,12,17],[10,151]),([0,2,3,4,33,43],[]),([0,2,3,4,38,43],[]),([0,2,3,4,12,75],[10]),([2,3,4,6,55,340],[0,4,13]),([0,2,3,4,45,55],[7]),([0,2,3,4,47,55],[]),([0,2,3,4,6,56],[0,156]),([2,3,4,6,12,340],[0,4]),([0,2,3,4,6,55],[0,24]),([0,2,3,4,45,59],[]),([0,2,3,4,47,59],[]),([0,2,3,4,6,78],[0]),([0,3,4,12,45,131],[6,10,11]),([0,2,3,4,12,60],[10,66]),([0,3,4,6,12,131],[6,10]),([0,2,3,4,12,72],[10]),([0,2,3,4,12,45],[10,161]),([2,3,4,6,33,326],[0,6,13]),([0,2,3,4,6,62],[0,166]),([2,3,4,6,12,326],[0,6]),([0,2,3,4,6,71],[0]),([0,2,3,4,6,33],[0,35]),([0,2,4,6,44,85],[1]),([2,4,6,44,85,87],[5,22,125]),([0,2,4,6,85,321],[1]),([0,4,6,85,87,111],[]),([0,4,41,85,87],[11,12,13,81,172]),([0,2,4,41,85,87],[81]),([0,4,6,41,85,87],[11,13,85]),([0,2,4,85,87,125],[81]),([0,2,4,45,85,87],[22]),([0,2,4,47,85,87],[11]),([0,2,4,6,87,88],[]),([0,2,4,6,87,89],[]),([0,2,4,6,85,90],[11]),([0,2,4,6,85,94],[11]),([0,3,4,41,85,111],[]),([0,2,6,14,85,111],[]),([0,2,3,45,85,111],[]),([0,2,3,6,88,111],[]),([0,2,3,4,24,85],[81]),([0,3,4,41,85,87],[81,172]),([0,2,4,14,41,85],[88]),([0,2,4,15,41,85],[81]),([0,2,4,41,85,253],[11,13]),([0,2,4,41,85,254],[11,13,81]),([0,2,3,4,85,247],[81]),([0,2,3,4,41,88],[12]),([0,2,3,4,41,89],[]),([0,2,4,6,85,254],[13,81]),([0,2,3,4,41,85],[81,173]),([0,2,4,14,85,125],[11]),([0,2,3,4,88,125],[]),([0,2,3,4,89,125],[]),([0,2,3,4,85,210],[81]),([2,3,4,6,85,340],[0,13]),([0,2,4,6,127,220],[0]),([2,3,4,6,127,293],[0]),([0,2,4,6,14,127],[]),([0,2,3,4,45,127],[]),([0,2,3,4,47,127],[]),([0,2,3,4,6,128],[0]),([0,2,4,6,85,224],[1]),([2,4,6,14,85,224],[5,8,88]),([0,2,4,6,85,323],[1]),([0,2,4,6,85,130],[11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_5 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_5 = true := by decide +kernel
def h26Block5_6 : List NodeSpec := nodesWithIdentity [([0,2,14,45,85],[6,7,11,81,86,181]),([0,2,4,14,45,85],[81]),([0,2,6,14,45,85],[6,11,85]),([0,2,4,14,47,85],[81]),([0,2,3,4,85,131],[81,108]),([0,2,4,45,60,85],[6,11,81]),([0,2,4,6,60,85],[6,81]),([0,2,3,4,85,135],[81]),([0,2,3,4,45,85],[81,182]),([2,3,4,6,88,327],[0,4,6]),([0,2,3,4,6,137],[0,185]),([2,3,4,6,85,327],[0,6]),([0,2,3,4,6,138],[0]),([0,2,3,4,6,88],[0,87]),([0,3,6,87,111,145],[]),([0,3,4,41,87,145],[]),([0,2,6,14,87,145],[]),([0,2,4,17,87,145],[]),([0,2,3,6,90,145],[11]),([0,2,3,4,22,145],[124]),([0,2,3,6,18,145],[1]),([2,3,6,18,111,145],[7,33,82]),([0,2,3,6,145,336],[1]),([0,3,41,111,145],[11,12,13,124,191]),([0,2,3,41,111,145],[124]),([0,3,6,41,111,145],[11,13,128]),([0,2,3,111,125,145],[124]),([0,2,3,17,111,145],[33]),([0,2,3,43,111,145],[11]),([0,2,3,6,122,145],[11]),([0,2,3,6,111,123],[]),([0,3,4,41,111,145],[124,191]),([0,2,3,14,41,145],[88]),([0,2,3,16,41,145],[124]),([0,2,3,4,145,254],[124]),([0,2,3,4,41,123],[]),([0,2,3,41,145,246],[11,13]),([0,2,3,41,145,247],[11,13,124]),([0,2,3,6,145,247],[13,124]),([0,2,3,4,41,145],[124,192]),([0,2,3,14,125,145],[11]),([0,2,3,4,145,199],[124]),([0,2,3,4,123,125],[]),([2,3,4,6,145,326],[0,13]),([2,3,4,6,160,238],[0]),([0,2,3,6,160,286],[0]),([0,2,3,6,14,160],[]),([0,2,3,4,17,160],[]),([0,2,3,4,43,160],[]),([0,2,3,4,6,161],[0]),([0,2,3,6,145,224],[1]),([2,3,6,14,145,224],[7,8,88]),([0,2,3,6,145,323],[1]),([0,2,3,6,130,145],[11]),([0,2,14,17,145],[4,5,11,124,129,198]),([0,2,3,14,17,145],[124]),([0,2,6,14,17,145],[4,11,128]),([0,2,3,14,43,145],[124]),([0,2,3,4,145,164],[124,142]),([0,2,3,17,39,145],[4,11,124]),([0,2,3,6,39,145],[4,124]),([0,2,3,4,145,165],[124]),([0,2,3,4,17,145],[124,199]),([2,3,4,6,145,327],[0,4]),([2,3,4,6,123,126],[0]),([0,2,3,6,123,286],[0]),([0,2,3,4,6,166],[0]),([0,2,3,4,6,189],[0]),([0,1,2,3,4,22],[124]),([2,3,4,6,44,55],[12,23,25,203])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_6 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_6 = true := by decide +kernel
def h26Block5_7 : List NodeSpec := nodesWithIdentity [([0,2,3,4,6,380],[0]),([1,2,3,4,6,340],[0]),([1,2,3,4,6,379],[0]),([0,1,6,14,87,111],[19,22,33,85,88,205]),([0,1,4,17,87,111],[33]),([0,1,3,45,87,111],[22]),([0,1,3,4,22,111],[124]),([0,1,3,4,24,87],[81]),([0,1,4,14,41,87],[88]),([0,1,4,15,41,87],[81]),([0,1,4,41,87,253],[12,13]),([0,1,4,41,87,254],[12,13,81]),([0,1,3,4,87,247],[81]),([0,1,3,4,41,90],[11]),([0,1,3,4,41,94],[]),([0,1,2,4,87,254],[0,10]),([0,1,4,17,41,87],[12,85,206,207]),([0,1,4,41,42,87],[10,81]),([0,1,3,4,41,87],[81,147]),([0,1,2,4,87,199],[0,10]),([0,1,2,14,45,87],[22]),([0,1,2,4,26,87],[10]),([0,1,2,4,14,22],[124]),([0,1,4,17,87,164],[4,5,10]),([0,1,2,4,39,87],[10,54]),([0,1,2,4,17,90],[11]),([0,1,2,4,17,94],[]),([0,1,3,4,87,164],[0,10]),([0,1,3,4,87,165],[0,10]),([0,1,2,4,17,87],[10,209]),([0,1,2,3,45,90],[11]),([0,1,2,3,4,30],[]),([0,1,2,3,4,96],[211]),([0,1,3,4,87,135],[81]),([0,1,2,4,72,87],[10]),([0,1,2,3,47,94],[]),([0,1,2,3,4,100],[]),([0,1,2,3,4,66],[]),([1,2,3,4,6,333],[1]),([0,2,3,4,6,182],[0]),([0,1,2,3,4,76],[]),([1,2,3,4,22,293],[124]),([0,1,2,3,4,340],[]),([1,2,3,4,22,340],[0,218]),([0,1,2,3,4,189],[]),([0,2,3,4,22,189],[0,220]),([0,1,2,3,4,164],[]),([0,1,3,4,22,164],[0,142]),([0,1,2,4,15,22],[124]),([0,1,2,3,4,254],[]),([0,1,2,4,22,254],[0]),([0,1,2,3,22,304],[]),([0,1,2,3,99],[]),([0,1,2,3,4,99],[]),([0,1,2,3,22,99],[124]),([0,1,2,3,6,99],[]),([0,1,2,3,87,99],[]),([0,2,3,4,6,176],[0]),([0,1,2,3,4,24],[81]),([2,3,4,6,18,33],[12,34,36,223]),([0,2,3,4,6,398],[0]),([1,2,3,4,6,326],[0]),([1,2,3,4,6,397],[0]),([0,1,3,14,41,111],[88]),([0,1,3,16,41,111],[124]),([0,1,3,4,111,254],[124]),([0,1,3,4,41,122],[]),([0,1,3,41,111,246],[12,13]),([0,1,3,41,111,247],[12,13,124]),([0,1,2,3,111,247],[0,10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_7 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_7 = true := by decide +kernel
def h26Block5_8 : List NodeSpec := nodesWithIdentity [([0,1,3,41,45,111],[12,128,150,206]),([0,1,3,41,46,111],[10,124]),([0,1,3,4,41,111],[124,149]),([0,1,2,3,111,210],[0,10]),([0,1,2,14,17,111],[33]),([0,1,2,3,26,111],[10]),([0,1,2,3,14,24],[81]),([0,1,2,3,4,154],[225]),([0,1,3,4,111,165],[124]),([0,1,2,4,43,122],[]),([0,1,2,3,75,111],[10]),([0,1,2,3,4,157],[]),([1,2,3,4,6,341],[1]),([0,2,3,4,6,190],[0]),([0,1,2,3,45,122],[]),([0,1,2,3,4,81],[]),([0,1,3,45,111,131],[6,7,10]),([0,1,2,3,60,111],[10,66]),([0,1,3,4,111,131],[0,10]),([0,1,3,4,111,135],[0,10]),([0,1,2,3,45,111],[10,229]),([1,2,3,4,24,238],[81]),([0,1,2,3,4,326],[]),([1,2,3,4,24,326],[0,231]),([0,1,2,3,4,176],[]),([0,2,3,4,24,176],[0,232]),([0,1,2,3,4,131],[]),([0,1,3,4,24,131],[0,108]),([0,1,2,3,16,24],[81]),([0,1,2,4,24,265],[]),([0,1,2,4,156],[]),([0,1,2,3,4,156],[]),([0,1,2,4,24,156],[81]),([0,1,2,3,4,247],[]),([0,1,2,3,24,247],[0]),([0,1,2,4,6,156],[]),([0,1,2,4,111,156],[]),([1,2,3,4,41,413],[81,124]),([0,2,3,4,41,415],[81,124]),([0,1,3,4,41,252],[81,124]),([0,1,2,13,14,41],[81,88]),([0,1,2,4,13,254],[]),([0,1,2,3,13,247],[]),([0,1,2,3,4,414],[81,124]),([0,1,2,3,4,416],[0,1,10]),([0,1,2,3,4,255],[]),([1,2,3,4,41,361],[81]),([0,2,3,4,41,266],[81]),([0,1,3,4,41,263],[81]),([0,1,2,3,15,247],[]),([0,1,2,3,4,142],[]),([0,1,2,3,4,267],[81]),([1,2,3,4,41,373],[124]),([0,2,3,4,41,308],[124]),([0,1,3,4,41,307],[124]),([0,1,2,4,16,254],[]),([0,1,2,3,4,168],[]),([0,1,2,3,4,309],[81]),([0,1,2,4,22,253],[88]),([0,1,2,3,41,264],[81]),([0,1,2,3,41,268],[]),([1,2,3,4,41,340],[0]),([0,2,3,4,41,189],[0]),([0,1,3,4,41,164],[0]),([0,1,2,3,41,304],[88]),([0,1,2,3,41,99],[]),([1,2,3,4,41,418],[0,81]),([0,2,3,4,41,419],[0,81]),([0,1,3,4,41,262],[0,81]),([0,1,2,4,129,254],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_8 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_8 = true := by decide +kernel
def h26Block5_9 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,269],[]),([0,1,2,4,41,303],[124]),([0,1,2,4,41,310],[]),([0,1,2,3,24,246],[88]),([1,2,3,4,41,326],[0]),([0,2,3,4,41,176],[0]),([0,1,3,4,41,131],[0]),([0,1,2,4,41,265],[88]),([0,1,2,4,41,156],[]),([1,2,3,4,41,421],[0,124]),([0,2,3,4,41,422],[0,124]),([0,1,3,4,41,306],[0,124]),([0,1,2,3,163,247],[]),([0,1,2,3,4,270],[]),([0,1,2,4,17,254],[0]),([1,2,3,4,41,385],[10,81]),([0,2,3,4,41,386],[10,81]),([0,1,2,4,42,254],[]),([0,1,2,3,45,247],[0]),([1,2,3,4,41,403],[10,124]),([0,2,3,4,41,404],[10,124]),([0,1,2,3,46,247],[]),([0,1,3,4,125,130],[]),([0,1,2,4,14,199],[124]),([0,1,2,3,14,210],[81]),([0,1,2,3,4,256],[]),([0,1,2,3,4,312],[]),([0,1,2,3,4,273],[]),([0,2,3,4,6,177],[0]),([0,1,2,3,4,26],[10]),([2,3,4,6,88,224],[5,89,91,245]),([0,2,3,4,6,424],[0]),([1,2,3,4,6,327],[0]),([1,2,3,4,6,423],[0]),([1,2,3,4,6,362],[1]),([0,2,3,4,6,271],[0]),([0,1,2,4,17,130],[]),([0,1,2,3,45,130],[]),([0,1,2,3,4,251],[]),([0,1,2,4,14,164],[124,142]),([0,1,2,14,17,39],[4,5,124]),([0,1,2,3,14,39],[0,81]),([0,1,2,14,17,45],[5,85,128,252]),([0,1,2,4,14,17],[124,250]),([0,1,2,3,14,75],[0,81]),([0,1,2,3,14,131],[81,108]),([0,1,2,14,45,60],[6,7,81]),([0,1,2,4,14,60],[0,81]),([0,1,2,4,14,72],[0,81]),([0,1,2,3,14,45],[81,253]),([1,2,3,4,26,126],[10]),([0,1,2,3,4,327],[]),([1,2,3,4,26,327],[0]),([0,2,3,4,26,82],[10]),([0,1,2,3,4,177],[]),([0,2,3,4,26,177],[0]),([0,1,3,4,26,194],[]),([0,1,3,4,195],[]),([0,1,2,3,4,195],[]),([0,1,3,4,26,195],[10]),([0,1,2,3,4,60],[]),([0,1,2,4,26,60],[0,66]),([0,1,2,3,4,39],[]),([0,1,2,3,26,39],[0,54]),([2,3,4,5,6,26],[256]),([0,1,3,4,6,195],[]),([0,1,3,4,14,195],[257]),([1,2,3,4,17,340],[0]),([0,2,3,4,17,189],[0]),([0,1,2,3,17,99],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_9 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_9 = true := by decide +kernel
def h26Block5_10 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,200],[]),([1,2,3,4,17,327],[0]),([0,2,3,4,17,177],[0]),([0,1,3,4,17,195],[]),([0,1,2,4,17,60],[0]),([0,1,2,3,4,201],[]),([0,1,2,3,39,45],[0]),([0,1,2,3,4,316],[]),([0,1,2,3,4,202],[]),([1,2,3,4,45,326],[0]),([0,2,3,4,45,176],[0]),([0,1,2,4,45,156],[]),([0,1,2,3,4,209],[]),([1,2,3,4,45,327],[0]),([0,2,3,4,45,177],[0]),([0,1,3,4,45,195],[]),([0,1,2,3,4,211],[]),([0,1,2,3,4,278],[]),([0,1,2,3,4,212],[]),([4,10,12,85,220],[4,5,12,13]),([3,4,10,12,145,220],[]),([1,3,4,10,12,17],[10]),([3,4,10,12,17,220],[5,11,281]),([1,3,4,10,12,178],[10]),([1,4,10,12,14,220],[]),([1,4,10,55,220],[0,4,13,22,24,282]),([1,3,4,10,55,220],[0]),([1,4,10,12,55,220],[13,22,26]),([1,3,4,10,59,220],[0]),([1,3,4,12,18,220],[]),([1,3,4,12,32,220],[]),([1,3,4,10,33,220],[5]),([1,3,4,10,38,220],[5]),([1,3,4,10,12,224],[13]),([1,3,4,10,12,225],[5]),([2,4,10,85,145,220],[]),([1,2,4,41,85,220],[81]),([2,4,10,41,85,220],[11,12,103]),([1,2,4,85,171,220],[81]),([1,4,10,85,111,220],[]),([1,2,4,10,55,220],[0]),([1,4,10,55,85,220],[4,22,39]),([1,2,4,10,127,220],[0]),([1,2,4,18,85,220],[4]),([1,2,4,32,85,220],[12]),([1,2,4,10,88,220],[12]),([1,2,4,10,89,220],[12]),([1,2,4,10,85,224],[]),([1,2,4,10,85,225],[]),([1,4,10,87,145,220],[5,12,22,43,96,284]),([1,3,10,111,145,220],[]),([1,2,10,14,145,220],[]),([1,2,3,18,145,220],[]),([1,2,3,10,145,224],[]),([1,4,10,41,87,220],[11,12,13,26,96,103,206]),([1,2,4,10,220,254],[11,81]),([1,4,87,171,220],[4,5,12]),([1,3,4,111,171,220],[]),([1,2,4,14,171,220],[12]),([1,2,3,4,215,220],[81]),([1,2,3,4,171,224],[]),([1,2,3,4,171,225],[]),([1,4,10,17,87,220],[4,5,11,16,18,47,281]),([1,3,4,10,164,220],[10,11]),([1,4,10,87,178],[5,12,13]),([1,2,4,10,87,178],[10]),([1,3,4,10,111,178],[5]),([1,3,4,10,120,178],[10]),([1,2,4,10,14,178],[]),([1,2,3,4,18,178],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_10 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_10 = true := by decide +kernel
def h26Block5_11 : List NodeSpec := nodesWithIdentity [([1,2,3,4,32,178],[]),([1,2,3,4,10,281],[10]),([1,4,10,55,87,220],[4,13,22,24,46,157,282]),([1,4,10,172,220],[11,22]),([1,4,18,87,220],[7,12,33,81,291,292]),([1,4,10,18,87,220],[7,12,33,34,72,103,291]),([1,4,32,87,220],[5,12,22]),([1,4,10,90,220],[0,22,33,88,212,291]),([1,4,10,87,90,220],[22,33,46,88,212,213,291]),([1,4,10,94,220],[5,12,22]),([1,4,10,87,224],[5,7,10,88,291,293]),([1,4,10,87,220,224],[5,7,88,91,281,291,293]),([1,4,10,87,225],[5,12,22]),([1,3,4,10,186,220],[5]),([1,10,14,111,220],[5,12,33,88]),([1,3,4,10,90,220],[0]),([1,4,10,90,111,220],[22,33,49]),([1,3,4,10,122,220],[0]),([1,3,10,111,224],[5,7,10,88,293,295]),([1,3,4,10,111,224],[10]),([1,3,10,111,220,224],[5,7,281]),([1,3,4,10,111,225],[10]),([1,2,4,10,174,220],[12]),([1,2,4,10,90,220],[0]),([1,4,10,14,90,220],[9,22,88]),([1,2,4,10,130,220],[0]),([1,2,14,18,220],[7,12,33,81,292,297]),([1,2,4,14,18,220],[81]),([1,2,10,14,18,220],[7,12,103]),([1,2,4,14,32,220],[81]),([1,2,3,4,176,220],[81,232]),([1,2,4,18,61,220],[7,12,81]),([1,2,4,10,61,220],[7,81]),([1,2,3,4,179,220],[81]),([1,2,3,4,18,220],[34,81]),([1,2,3,4,10,177],[10]),([1,3,4,10,133,224],[5,7,10]),([1,3,4,10,133,220],[7,10]),([1,2,3,4,10,180],[10]),([1,2,3,4,10,224],[10,91]),([3,4,10,12,85,286],[]),([3,10,12,145,286],[6,7,12,13]),([1,3,4,10,12,45],[10]),([3,4,10,12,45,286],[7,11,305]),([1,3,4,10,12,175],[10]),([1,3,10,12,14,286],[]),([1,3,4,12,44,286],[]),([1,3,4,12,54,286],[]),([1,3,4,10,55,286],[7]),([1,3,4,10,59,286],[7]),([1,3,4,10,12,239],[7]),([1,3,10,33,286],[0,6,13,33,35,306]),([1,3,4,10,33,286],[0]),([1,3,10,12,33,286],[13,26,33]),([1,3,4,10,38,286],[0]),([2,3,10,85,145,286],[]),([1,4,10,85,87,286],[]),([1,3,10,85,111,286],[7,12,33,39,132,307]),([1,2,10,14,85,286],[]),([1,2,4,44,85,286],[]),([1,2,3,10,88,286],[12]),([1,2,3,41,145,286],[124]),([2,3,10,41,145,286],[11,12,137]),([1,2,3,145,171,286],[124]),([1,3,10,87,145,286],[]),([1,2,3,10,33,286],[0]),([1,3,10,33,145,286],[6,33,43]),([1,2,3,10,160,286],[0]),([1,2,3,44,145,286],[6]),([1,2,3,54,145,286],[12])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_11 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_11 = true := by decide +kernel
def h26Block5_12 : List NodeSpec := nodesWithIdentity [([1,2,3,10,123,286],[12]),([1,2,3,10,145,239],[]),([1,3,10,41,111,286],[11,12,13,26,132,137,206]),([1,2,3,10,247,286],[11,124]),([1,3,4,87,171,286],[]),([1,3,111,171,286],[6,7,12]),([1,2,3,14,171,286],[12]),([1,2,3,4,204,286],[124]),([1,2,3,4,171,239],[]),([1,3,10,45,111,286],[6,7,11,28,30,50,305]),([1,3,4,10,131,286],[10,11]),([1,3,4,10,87,175],[7]),([1,3,4,10,108,175],[10]),([1,3,10,111,175],[7,12,13]),([1,2,3,10,111,175],[10]),([1,2,3,10,14,175],[]),([1,2,3,4,44,175],[]),([1,2,3,4,54,175],[]),([1,2,3,4,10,280],[10]),([1,3,4,10,172,286],[7]),([1,10,14,87,286],[7,12,22,88]),([1,3,4,10,87,224],[10]),([1,4,10,87,224,286],[5,7,305]),([1,3,4,10,87,239],[10]),([1,3,10,90,286],[0,22,33,88,212,314]),([1,3,4,10,90,286],[0]),([1,3,10,87,90,286],[22,33,46]),([1,3,4,10,94,286],[0]),([1,3,10,33,111,286],[6,13,33,35,49,167,306]),([1,3,10,186,286],[11,33]),([1,3,44,111,286],[5,12,22,124,315,316]),([1,3,10,44,111,286],[5,12,22,23,60,137,315]),([1,3,54,111,286],[7,12,33]),([1,3,10,90,111,286],[22,33,49,88,212,213,314]),([1,3,10,122,286],[5,12,33]),([1,3,10,111,224,286],[5,7,88,91,293,295,305]),([1,3,10,111,239],[7,12,22]),([1,2,3,10,174,286],[12]),([1,2,3,10,90,286],[0]),([1,3,10,14,90,286],[9,33,88]),([1,2,3,10,130,286],[0]),([1,2,14,44,286],[5,12,22,124,316,318]),([1,2,3,14,44,286],[124]),([1,2,10,14,44,286],[5,12,137]),([1,2,3,14,54,286],[124]),([1,2,3,4,189,286],[124,220]),([1,2,3,44,51,286],[5,12,124]),([1,2,3,10,51,286],[5,124]),([1,2,3,4,192,286],[124]),([1,2,3,4,44,286],[23,124]),([1,3,4,10,133,286],[5,10]),([1,3,4,10,83,239],[10]),([1,2,3,4,10,193],[10]),([1,2,3,10,111,239],[10]),([0,3,4,10,12,17],[10]),([3,4,10,12,17,85],[4,11,307]),([0,3,4,10,12,328],[10]),([0,4,10,12,14,85],[]),([0,4,12,44,85],[1,5,12,21,22,322]),([0,3,4,12,44,85],[1]),([0,4,10,12,44,85],[2,12,22]),([0,3,4,12,54,85],[1]),([0,3,4,12,18,85],[4]),([0,3,4,12,32,85],[12]),([0,3,4,10,33,85],[]),([0,3,4,10,38,85],[]),([0,3,4,10,12,88],[12]),([0,3,4,10,12,89],[12]),([0,3,4,10,12,45],[10]),([3,4,10,12,45,145],[6,11,284])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_12 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_12 = true := by decide +kernel
def h26Block5_13 : List NodeSpec := nodesWithIdentity [([0,3,4,10,12,324],[10]),([0,3,10,12,14,145],[]),([0,3,4,12,44,145],[6]),([0,3,4,12,54,145],[12]),([0,3,4,10,55,145],[]),([0,3,4,10,59,145],[]),([0,3,4,10,12,123],[12]),([0,3,12,18,145],[1,7,12,32,33,323]),([0,3,4,12,18,145],[1]),([0,3,10,12,18,145],[2,12,33]),([0,3,4,12,32,145],[1]),([0,1,4,12,14,44],[]),([0,1,4,10,14,55],[]),([0,1,3,12,14,18],[]),([0,1,3,10,14,33],[]),([0,1,3,4,12,28],[1]),([0,1,3,4,10,19],[0]),([0,3,4,12,44,189],[1,12,22]),([0,1,3,4,33,44],[5]),([0,1,3,4,38,44],[]),([0,1,3,4,12,51],[1,59]),([0,3,4,10,12,189],[1,22]),([0,1,3,4,12,44],[1,324]),([0,1,3,4,33,54],[]),([0,1,3,4,38,54],[]),([0,1,3,4,12,77],[1]),([1,3,4,10,55,340],[0,13,22]),([0,1,3,4,18,55],[7]),([0,1,3,4,32,55],[]),([0,1,3,4,10,56],[0,156]),([1,3,4,10,12,340],[0,22]),([0,1,3,4,10,55],[0,24]),([0,1,3,4,18,59],[]),([0,1,3,4,32,59],[]),([0,1,3,4,10,78],[0]),([0,3,4,12,18,176],[1,12,33]),([0,1,3,4,12,61],[1,71]),([0,3,4,10,12,176],[1,33]),([0,1,3,4,12,70],[1]),([0,1,3,4,12,18],[1,331]),([1,3,4,10,33,326],[0,13,33]),([0,1,3,4,10,62],[0,166]),([1,3,4,10,12,326],[0,33]),([0,1,3,4,10,71],[0]),([0,1,3,4,10,33],[0,35]),([0,1,3,4,10,164],[0]),([1,4,10,17,85,87],[4,5,307]),([1,3,4,10,17,55],[11,18,157,338]),([0,1,3,4,10,347],[0]),([0,4,10,85,87,145],[]),([0,3,10,85,111,145],[]),([0,2,10,14,85,145],[2,4,6,88,103,340]),([0,2,4,44,85,145],[6]),([0,2,3,18,85,145],[4]),([0,1,2,4,85,254],[0,1]),([0,4,10,41,85,87],[12,13,103]),([0,2,4,41,44,85],[2,11,103,322]),([0,2,4,41,53,85],[1,81]),([0,1,2,4,85,204],[0,1]),([0,1,4,10,17,87],[10]),([0,1,4,10,87,328],[10]),([0,1,4,41,85,87],[81]),([0,1,4,85,87,171],[81]),([0,1,4,18,85,87],[4]),([0,1,4,32,85,87],[12]),([0,1,4,10,87,88],[12]),([0,1,4,10,87,89],[12]),([0,1,4,10,85,90],[]),([0,1,4,10,85,94],[]),([0,1,10,14,85,111],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_13 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_13 = true := by decide +kernel
def h26Block5_14 : List NodeSpec := nodesWithIdentity [([0,1,4,44,85,111],[]),([0,1,3,10,88,111],[12]),([1,2,3,4,10,340],[0]),([1,2,3,4,10,346],[0]),([0,1,2,14,18,85],[4]),([0,1,2,4,28,85],[1]),([0,2,4,44,85,189],[1,5,22]),([0,1,2,4,51,85],[1,59]),([0,1,2,4,44,88],[12]),([0,1,2,4,44,89],[]),([0,2,3,4,85,189],[0,1]),([0,2,3,4,85,192],[0,1]),([0,1,2,4,44,85],[1,341]),([0,1,2,3,18,88],[12]),([0,1,2,3,4,106],[343]),([0,2,3,4,85,179],[81]),([0,1,2,4,70,85],[1]),([0,1,2,3,32,89],[]),([0,1,2,3,4,107],[]),([0,1,2,3,4,63],[]),([1,2,3,4,10,330],[10]),([0,1,3,4,10,138],[0]),([0,1,2,3,4,73],[]),([0,1,2,3,10,99],[]),([0,1,2,3,85,99],[]),([0,1,3,4,10,131],[0]),([1,3,10,45,111,145],[6,7,284]),([1,3,4,10,33,45],[11,30,167,347]),([0,1,3,4,10,353],[0]),([0,1,2,3,145,247],[0,1]),([0,3,10,41,111,145],[12,13,137]),([0,2,3,18,41,145],[2,11,137,348]),([0,2,3,31,41,145],[1,124]),([0,1,2,3,145,215],[0,1]),([0,1,10,14,87,145],[]),([0,1,3,18,87,145],[]),([0,1,3,10,90,145],[]),([0,1,3,10,45,111],[10]),([0,1,3,10,111,324],[10]),([0,1,3,41,111,145],[124]),([0,1,3,111,145,171],[124]),([0,1,3,44,111,145],[6]),([0,1,3,54,111,145],[12]),([0,1,3,10,122,145],[]),([0,1,3,10,111,123],[12]),([1,2,3,4,10,326],[0]),([1,2,3,4,10,352],[0]),([0,1,2,14,44,145],[6]),([0,1,2,3,28,145],[1]),([0,1,2,3,4,158],[349]),([0,2,3,4,145,192],[124]),([0,1,2,4,54,123],[]),([0,1,2,3,77,145],[1]),([0,1,2,3,4,159],[]),([1,3,4,9,10,123],[0]),([1,2,3,4,10,343],[10]),([0,1,3,4,10,166],[0]),([0,1,2,3,18,123],[]),([0,1,2,3,4,79],[]),([0,2,3,18,145,176],[1,7,33]),([0,1,2,3,61,145],[1,71]),([0,2,3,4,145,176],[0,1]),([0,2,3,4,145,179],[0,1]),([0,1,2,3,18,145],[1,351]),([0,1,2,4,10,156],[]),([0,1,2,4,145,156],[]),([0,1,4,10,87,254],[13,81]),([0,1,3,10,111,247],[13,124]),([0,1,2,4,44,254],[0]),([1,2,3,4,41,457],[1,81])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_14 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_14 = true := by decide +kernel
def h26Block5_15 : List NodeSpec := nodesWithIdentity [([0,1,3,4,41,358],[1,81,324]),([0,1,2,4,53,254],[]),([0,1,2,3,18,247],[0]),([1,2,3,4,41,465],[1,124]),([0,1,3,4,41,372],[1,124,331]),([0,1,2,3,31,247],[]),([0,1,4,14,87,171],[12]),([0,1,3,4,90,171],[]),([0,1,3,4,94,171],[]),([0,1,3,4,87,215],[81]),([0,1,3,14,111,171],[12]),([0,1,3,4,122,171],[]),([0,1,3,4,111,204],[124]),([0,2,3,4,171,174],[]),([0,1,2,4,14,204],[124]),([0,1,2,3,14,215],[81]),([0,1,2,3,4,438],[]),([0,1,2,3,4,447],[]),([0,1,2,3,4,439],[]),([1,3,4,10,87,340],[0,13]),([0,1,4,10,172,220],[0]),([1,3,4,10,172,293],[0]),([0,1,4,10,14,172],[]),([0,1,3,4,18,172],[]),([0,1,3,4,32,172],[]),([0,1,3,4,10,173],[0]),([0,1,4,10,87,224],[10]),([1,4,10,14,87,224],[5,51,88]),([0,1,4,10,87,323],[10]),([0,1,4,10,87,174],[12]),([0,1,14,18,87],[7,12,33,81,292,364]),([0,1,4,14,18,87],[81]),([0,1,10,14,18,87],[12,33,103]),([0,1,4,14,32,87],[81]),([0,1,3,4,87,176],[81,232]),([0,1,4,18,61,87],[12,33,81]),([0,1,4,10,61,87],[33,81]),([0,1,3,4,87,179],[81]),([0,1,3,4,18,87],[81,365]),([1,3,4,10,90,332],[0,22,33]),([0,1,3,4,10,181],[0,368]),([1,3,4,10,87,332],[0,33]),([0,1,3,4,10,182],[0]),([0,1,3,4,10,90],[0,212]),([1,3,4,10,111,326],[0,13]),([1,3,4,10,186,238],[0]),([0,1,3,10,186,286],[0]),([0,1,3,10,14,186],[]),([0,1,3,4,44,186],[]),([0,1,3,4,54,186],[]),([0,1,3,4,10,187],[0]),([0,1,3,10,111,224],[10]),([1,3,10,14,111,224],[7,51,88]),([0,1,3,10,111,323],[10]),([0,1,3,10,111,174],[12]),([0,1,14,44,111],[5,12,22,124,316,371]),([0,1,3,14,44,111],[124]),([0,1,10,14,44,111],[12,22,137]),([0,1,3,14,54,111],[124]),([0,1,3,4,111,189],[124,220]),([0,1,3,44,51,111],[12,22,124]),([0,1,3,10,51,111],[22,124]),([0,1,3,4,111,192],[124]),([0,1,3,4,44,111],[124,372]),([1,3,4,10,111,332],[0,22]),([0,1,3,4,10,190],[0]),([0,1,3,4,10,133],[0]),([0,1,2,3,4,28],[1]),([1,3,4,10,90,224],[5,91,213,375]),([0,1,3,4,10,365],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_15 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_15 = true := by decide +kernel
def h26Block5_16 : List NodeSpec := nodesWithIdentity [([1,2,3,4,10,423],[10]),([0,1,3,4,10,276],[0]),([0,1,2,4,44,174],[]),([0,1,2,3,18,174],[]),([0,1,2,3,4,427],[]),([1,2,3,4,10,332],[0]),([1,2,3,4,10,362],[0]),([0,1,2,4,14,189],[124,220]),([0,1,2,14,44,51],[5,22,124]),([0,1,2,3,14,51],[0,81]),([0,1,2,14,18,44],[5,103,137,380]),([0,1,2,4,14,44],[124,378]),([0,1,2,3,14,77],[0,81]),([0,1,2,3,14,176],[81,232]),([0,1,2,14,18,61],[7,33,81]),([0,1,2,4,14,61],[0,81]),([0,1,2,4,14,70],[0,81]),([0,1,2,3,14,18],[81,381]),([1,2,3,4,7,28],[1]),([0,1,2,3,4,332],[]),([1,2,3,4,28,332],[0,383]),([0,1,3,4,28,83],[1]),([0,2,3,4,28,196],[]),([0,2,3,4,197],[]),([0,1,2,3,4,197],[]),([0,2,3,4,28,197],[1]),([0,1,2,3,4,133],[]),([0,1,3,4,28,133],[0]),([0,1,2,3,4,61],[]),([0,1,2,4,28,61],[0,71]),([0,1,2,3,4,51],[]),([0,1,2,3,28,51],[0,59]),([1,3,4,9,10,28],[385]),([0,2,3,4,10,197],[]),([0,2,3,4,14,197],[386]),([1,2,3,4,44,340],[0]),([0,1,3,4,44,164],[0]),([0,1,2,3,44,99],[]),([0,1,2,3,4,205],[]),([1,2,3,4,44,332],[0]),([0,2,3,4,44,197],[]),([0,1,3,4,44,133],[0]),([0,1,2,4,44,61],[0]),([0,1,2,3,4,206],[]),([0,1,2,3,18,51],[0]),([0,1,2,3,4,450],[]),([0,1,2,3,4,207],[]),([1,2,3,4,18,326],[0]),([0,1,3,4,18,131],[0]),([0,1,2,4,18,156],[]),([0,1,2,3,4,214],[]),([1,2,3,4,18,332],[0]),([0,2,3,4,18,197],[]),([0,1,3,4,18,133],[0]),([0,1,2,3,4,216],[]),([0,1,2,3,4,444],[]),([0,1,2,3,4,217],[]),([2,4,12,85,220,286],[]),([2,3,12,145,220,286],[]),([1,4,12,87,220,286],[]),([1,3,12,111,220,286],[]),([1,2,12,14,220,286],[5,7,26,88,178,413]),([1,2,4,55,220,286],[7]),([1,2,3,33,220,286],[5]),([2,85,145,220,286],[4,5,6,7]),([1,2,4,45,85,220],[81]),([2,4,45,85,220,286],[7,11,414]),([1,2,4,85,175,220],[81]),([1,2,85,111,220,286],[]),([1,2,4,127,220,286],[7])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_16 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_16 = true := by decide +kernel
def h26Block5_17 : List NodeSpec := nodesWithIdentity [([1,2,4,85,134,286],[]),([1,2,4,85,132,220],[7]),([1,2,88,220,286],[0,4,6,87,88,417]),([1,2,4,88,220,286],[0]),([1,2,85,88,220,286],[4,39,88]),([1,2,4,89,220,286],[0]),([1,2,3,17,145,286],[124]),([2,3,17,145,220,286],[5,11,145]),([1,2,3,145,178,286],[124]),([1,2,87,145,220,286],[]),([1,2,3,160,220,286],[5]),([1,2,3,134,145,286],[5]),([1,2,3,132,145,220],[]),([1,2,3,88,220,286],[0]),([1,2,88,145,220,286],[6,43,88]),([1,2,3,123,220,286],[0]),([1,2,14,17,220,286],[4,5,11,18,85,140,145]),([1,2,3,39,220,286],[11,124]),([1,2,4,87,178,286],[]),([1,2,3,111,178,286],[5]),([1,2,3,124,178,286],[124]),([1,2,3,4,203,286],[124]),([1,2,3,4,132,178],[]),([1,2,14,178,286],[5,6,7]),([1,2,4,14,178,286],[124]),([1,2,14,45,220,286],[6,7,11,30,86,106,414]),([1,2,4,60,220,286],[11,81]),([1,2,4,87,175,220],[7]),([1,2,4,109,175,220],[81]),([1,2,3,111,175,220],[]),([1,2,3,4,213,220],[81]),([1,2,3,4,134,175],[]),([1,2,14,175,220],[4,5,7]),([1,2,3,14,175,220],[81]),([1,2,4,172,220,286],[7]),([1,87,111,220,286],[5,7,22,33]),([1,2,4,18,87,220],[81]),([1,4,18,87,220,286],[7,12,414]),([1,2,4,87,132,220],[81]),([1,2,90,220,286],[0,22,33,88,212,420]),([1,2,4,90,220,286],[0]),([1,2,87,90,220,286],[22,46,88]),([1,2,4,94,220,286],[0]),([1,2,3,186,220,286],[5]),([1,2,3,44,111,286],[124]),([1,3,44,111,220,286],[5,12,145]),([1,2,3,111,134,286],[124]),([1,2,3,90,220,286],[0]),([1,2,90,111,220,286],[33,49,88]),([1,2,3,122,220,286],[0]),([1,2,14,44,220,286],[5,12,22,23,103,145,318]),([1,2,3,51,220,286],[12,124]),([1,2,3,134,170,286],[124]),([1,2,3,4,198,286],[124]),([1,2,14,134,286],[5,7,33]),([1,2,4,14,134,286],[124]),([1,2,14,18,220,286],[7,12,33,34,292,297,414]),([1,2,4,61,220,286],[12,81]),([1,2,4,132,143,220],[81]),([1,2,3,4,208,220],[81]),([1,2,14,132,220],[5,7,22]),([1,2,3,14,132,220],[81]),([1,2,14,88,220,286],[4,6,9,87,88,186,417]),([1,2,174,220,286],[11,88]),([1,2,14,90,220,286],[9,22,33,88,212,214,420]),([1,2,130,220,286],[12,88]),([0,1,2,4,220,254],[0]),([2,4,12,41,85,220],[11,13,178]),([1,4,12,41,87,220],[12,13,178]),([1,2,4,41,55,220],[11,26,178,282])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_17 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_17 = true := by decide +kernel
def h26Block5_18 : List NodeSpec := nodesWithIdentity [([1,2,4,41,58,220],[0,81]),([0,1,2,4,220,348],[0]),([0,2,4,41,85,220],[81]),([0,2,4,85,220,320],[81]),([0,4,12,85,111,220],[]),([0,2,4,12,44,85],[1]),([0,4,12,44,85,220],[5,22,76]),([0,2,4,12,85,134],[1]),([0,2,4,33,85,220],[5]),([0,2,4,38,85,220],[5]),([0,2,4,12,88,220],[]),([0,2,4,12,89,220],[]),([0,2,4,12,85,224],[13]),([0,2,4,12,85,225],[5]),([0,4,12,87,145,220],[]),([0,3,12,111,145,220],[6,13,33,76,191,281]),([0,2,12,14,145,220],[]),([0,2,4,55,145,220],[]),([0,2,3,12,145,224],[13]),([0,1,3,4,12,164],[0,1]),([0,4,12,17,87,220],[4,5,281]),([0,3,4,12,17,44],[11,17,60,423]),([0,1,3,4,12,203],[0,1]),([0,1,4,41,87,220],[81]),([0,1,4,87,220,320],[81]),([0,1,4,12,17,87],[10]),([0,1,4,12,87,178],[10]),([0,1,4,33,87,220],[5]),([0,1,4,38,87,220],[5]),([0,1,4,12,90,220],[]),([0,1,4,12,94,220],[]),([0,1,4,12,87,224],[13]),([0,1,4,12,87,225],[5]),([0,1,12,14,111,220],[]),([0,1,4,55,111,220],[]),([0,1,3,12,111,224],[13]),([0,2,3,4,12,189],[0,1]),([0,2,3,4,12,198],[0,1]),([0,1,2,14,33,220],[5]),([0,1,2,4,19,220],[0]),([1,2,4,55,220,340],[0,4,22]),([0,1,2,4,56,220],[0,156]),([0,1,2,4,55,224],[7]),([0,1,2,4,55,225],[]),([1,2,3,4,220,340],[0]),([1,2,3,4,220,342],[0]),([0,1,2,4,55,220],[0,24]),([0,1,2,3,33,224],[5]),([0,1,2,3,4,233],[426]),([1,2,3,4,220,329],[81]),([0,1,2,4,71,220],[0]),([0,1,2,3,38,225],[]),([0,1,2,3,4,234],[]),([0,1,2,3,4,65],[]),([0,2,3,4,12,180],[10]),([0,1,3,4,12,136],[1]),([0,1,2,3,4,74],[]),([0,1,2,3,12,99],[]),([1,2,4,22,219,220],[428]),([0,1,2,3,99,220],[]),([0,2,4,45,85,220],[81]),([2,4,45,85,145,220],[6,11,285]),([0,2,4,85,220,324],[81]),([0,2,85,111,145,220],[]),([0,2,4,127,145,220],[]),([0,2,4,85,160,220],[5]),([0,2,4,85,134,145],[5]),([0,2,85,145,224],[1,5,7,88,90,431]),([0,2,4,85,145,224],[1]),([0,2,85,145,220,224],[5,76,88])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_18 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_18 = true := by decide +kernel
def h26Block5_19 : List NodeSpec := nodesWithIdentity [([0,2,4,85,145,225],[1]),([0,1,2,88,111,220],[]),([0,1,2,85,111,224],[]),([1,2,4,85,220,340],[0,22]),([1,2,4,127,220,293],[0]),([0,1,2,4,128,220],[0]),([0,1,2,4,127,224],[]),([0,1,2,4,127,225],[]),([0,2,4,85,189,220],[1,22]),([0,2,4,85,134,153],[1]),([0,1,2,4,88,134],[]),([0,1,2,4,89,134],[]),([0,1,2,4,85,240],[1]),([1,2,4,88,220,327],[0,4,88]),([0,1,2,4,137,220],[0,185]),([1,2,4,85,220,327],[0,88]),([0,1,2,4,138,220],[0]),([0,1,2,4,88,220],[0,87]),([0,2,4,85,177,224],[1,5,88]),([0,1,2,4,85,133],[1]),([0,2,4,85,177,220],[1,88]),([0,1,2,4,85,136],[1]),([0,1,2,4,85,224],[1,437]),([0,1,2,4,60,220],[0]),([1,2,14,45,145,220],[6,7,285]),([1,2,4,45,88,220],[11,30,186,439]),([0,1,2,4,220,368],[0]),([0,1,2,3,39,145],[0,1]),([0,2,14,17,145,220],[4,5,145]),([0,2,3,17,145,224],[11,17,145,440]),([0,1,2,3,145,281],[0,1]),([0,1,87,111,145,220],[]),([0,1,2,90,145,220],[]),([0,1,2,87,145,224],[]),([1,2,4,160,219,220],[0]),([1,2,3,4,220,352],[81]),([0,1,3,4,134,160],[]),([0,1,2,14,160,220],[5]),([0,1,2,4,161,220],[0]),([0,1,2,3,160,224],[]),([0,1,2,3,4,250],[]),([0,2,3,134,144,145],[1]),([0,2,3,4,145,198],[124]),([0,1,2,14,134,145],[5]),([0,1,2,3,145,240],[1]),([0,1,2,3,4,257],[]),([0,1,2,14,45,220],[81]),([0,1,2,14,220,324],[81]),([0,1,2,14,17,145],[124]),([0,1,2,14,145,178],[124]),([0,1,2,130,145,220],[]),([1,2,3,4,220,327],[0]),([1,2,3,4,220,343],[0]),([0,2,3,145,177,224],[1,7,88]),([0,1,2,3,133,145],[1]),([0,2,3,4,145,177],[0,1]),([0,2,3,4,145,180],[0,1]),([0,1,2,3,145,224],[1,442]),([0,1,3,4,145,195],[444]),([0,1,3,4,195,220],[257]),([0,1,4,87,164,220],[4,10]),([0,1,2,14,39,220],[4,124]),([0,1,2,3,39,224],[0]),([0,1,4,87,111,178],[5]),([0,1,4,87,120,178],[10]),([0,1,2,4,90,178],[]),([0,1,2,4,94,178],[]),([0,1,2,4,87,281],[10]),([1,2,3,4,178,410],[]),([0,2,3,4,178,411],[10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_19 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_19 = true := by decide +kernel
def h26Block5_20 : List NodeSpec := nodesWithIdentity [([0,1,3,110,111,178],[10]),([0,1,2,4,149,178],[]),([0,1,2,3,4,500],[1]),([0,2,3,4,178,186],[]),([0,1,3,4,111,203],[124]),([0,1,2,14,111,178],[5]),([0,1,2,3,111,281],[10]),([0,1,2,3,4,440],[]),([1,2,3,4,178,454],[]),([0,1,3,4,120,203],[]),([0,1,2,4,178,185],[]),([0,1,2,3,4,441],[]),([1,2,3,4,178,465],[]),([0,1,2,14,124,178],[124]),([0,1,2,4,178,311],[]),([0,1,2,3,124,281],[]),([0,1,2,3,4,481],[]),([0,1,2,4,14,203],[124]),([0,1,2,3,4,482],[]),([0,1,2,4,130,178],[]),([0,1,2,3,170,281],[]),([0,1,2,3,4,442],[]),([1,2,4,87,220,340],[0,4]),([1,2,4,172,220,293],[0]),([0,1,4,111,172,220],[]),([0,1,2,4,173,220],[0]),([0,1,2,4,172,224],[]),([0,1,2,4,172,225],[]),([0,1,4,18,87,220],[81]),([1,4,18,87,111,220],[12,33,97]),([0,1,4,87,220,336],[81]),([0,1,4,87,186,220],[5]),([0,1,87,111,224],[5,7,10,88,293,452]),([0,1,4,87,111,224],[10]),([0,1,87,111,220,224],[5,88,281]),([0,1,4,87,111,225],[10]),([1,2,4,90,220,332],[0,22,88]),([0,1,2,4,181,220],[0,368]),([1,2,4,87,220,332],[0,88]),([0,1,2,4,182,220],[0]),([0,1,2,4,90,220],[0,212]),([0,1,2,4,87,177],[10]),([0,1,4,87,133,224],[5,10,88]),([0,1,4,87,133,220],[10,88]),([0,1,2,4,87,180],[10]),([0,1,2,4,87,224],[10,455]),([0,1,2,4,61,220],[0]),([1,2,14,18,111,220],[7,33,97]),([1,2,4,18,90,220],[12,34,214,457]),([0,1,2,4,220,337],[0]),([1,2,4,186,219,220],[0]),([1,2,3,4,220,397],[81]),([0,1,2,14,186,220],[5]),([0,1,2,4,187,220],[0]),([0,1,2,3,186,224],[]),([0,1,2,3,4,401],[]),([0,1,2,3,51,111],[0,10]),([0,1,14,44,111,220],[5,22,145]),([0,1,3,44,111,224],[12,60,145,459]),([0,1,2,3,111,240],[0,10]),([0,1,2,14,18,220],[81]),([0,1,2,14,220,336],[81]),([0,1,2,111,174,220],[]),([0,1,2,14,44,111],[124]),([0,1,2,14,111,134],[124]),([1,2,3,4,220,332],[0]),([1,2,3,4,220,341],[0]),([0,1,2,3,111,177],[10]),([0,1,3,111,133,224],[7,10,88]),([0,1,3,4,111,133],[0,10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_20 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_20 = true := by decide +kernel
def h26Block5_21 : List NodeSpec := nodesWithIdentity [([0,1,3,4,111,136],[0,10]),([0,1,2,3,111,224],[10,460]),([0,2,3,4,111,197],[462]),([0,2,3,4,197,220],[386]),([0,1,2,14,51,220],[22,124]),([0,1,2,3,51,224],[0]),([1,2,3,4,134,287],[]),([0,1,3,4,134,235],[1]),([0,1,2,4,114,134],[]),([0,1,2,3,4,499],[1]),([1,2,3,4,134,335],[]),([0,2,3,4,153,198],[]),([0,1,2,4,134,141],[]),([0,1,2,3,4,274],[]),([1,2,3,4,134,403],[]),([0,1,2,14,134,170],[124]),([0,1,2,4,134,315],[]),([0,1,2,3,170,240],[]),([0,1,2,3,4,485],[]),([0,1,2,4,14,198],[124]),([0,1,2,3,4,486],[]),([0,1,2,4,134,174],[]),([0,1,2,3,4,275],[]),([1,2,4,14,220,327],[0,4]),([0,1,2,4,220,276],[0]),([1,2,4,14,220,332],[0,22]),([0,1,2,4,220,271],[0]),([1,2,3,4,224,327],[0]),([0,2,3,4,26,260],[469]),([0,1,3,4,195,224],[]),([0,1,2,4,60,224],[0]),([0,2,3,4,8,177],[]),([1,2,3,4,126,177],[]),([0,2,3,4,11,177],[]),([0,2,3,4,83,177],[]),([0,2,3,4,85,177],[0,1]),([0,2,3,4,121,177],[]),([0,2,3,4,153,177],[]),([0,1,2,4,109,177],[]),([0,1,2,3,124,177],[]),([0,1,2,3,4,279],[]),([0,2,3,4,177,229],[]),([1,2,3,4,224,332],[0]),([0,2,3,4,197,224],[]),([0,1,3,4,28,242],[470]),([0,1,2,4,61,224],[0]),([1,2,3,4,7,133],[]),([0,1,3,4,133,218],[]),([0,1,3,4,11,133],[]),([0,1,3,4,82,133],[]),([0,1,2,4,133,143],[]),([0,1,2,3,133,170],[]),([0,1,2,3,4,282],[]),([0,1,3,4,87,133],[0,10]),([0,1,3,4,108,133],[]),([0,1,3,4,120,133],[]),([0,1,3,4,133,230],[]),([1,2,4,177,219,220],[0]),([0,2,3,4,177,232],[]),([1,2,4,133,219,220],[0]),([0,1,3,4,133,228],[]),([0,1,2,3,4,445],[]),([0,1,2,3,4,283],[]),([0,1,2,3,247,286],[0]),([2,3,12,41,145,286],[11,13,195]),([1,3,12,41,111,286],[12,13,195]),([1,2,3,33,41,286],[11,26,195,471]),([1,2,3,37,41,286],[0,124]),([0,1,2,3,286,355],[0]),([0,4,12,85,87,286],[4,13,22,116,172,305])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_21 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_21 = true := by decide +kernel
def h26Block5_22 : List NodeSpec := nodesWithIdentity [([0,3,12,85,111,286],[]),([0,2,12,14,85,286],[]),([0,2,3,33,85,286],[]),([0,2,3,12,88,286],[]),([0,2,3,41,145,286],[124]),([0,2,3,145,286,320],[124]),([0,3,12,87,145,286],[]),([0,2,3,12,18,145],[1]),([0,3,12,18,145,286],[7,33,116]),([0,2,3,12,132,145],[1]),([0,2,3,55,145,286],[7]),([0,2,3,59,145,286],[7]),([0,2,3,12,123,286],[]),([0,2,3,12,145,239],[7]),([0,1,3,4,12,131],[0,1]),([0,3,12,45,111,286],[6,7,305]),([0,3,4,12,18,45],[11,29,72,472]),([0,1,3,4,12,213],[0,1]),([0,1,12,14,87,286],[]),([0,1,3,33,87,286],[]),([0,1,3,12,90,286],[]),([0,1,3,41,111,286],[124]),([0,1,3,111,286,320],[124]),([0,1,3,12,45,111],[10]),([0,1,3,12,111,175],[10]),([0,1,3,55,111,286],[7]),([0,1,3,59,111,286],[7]),([0,1,3,12,122,286],[]),([0,1,3,12,111,239],[7]),([0,2,3,4,12,176],[0,1]),([0,2,3,4,12,208],[0,1]),([0,1,2,14,55,286],[7]),([0,1,2,3,19,286],[0]),([0,1,2,3,4,296],[473]),([1,2,3,4,286,342],[124]),([0,1,2,4,59,239],[]),([0,1,2,3,78,286],[0]),([0,1,2,3,4,297],[]),([0,3,4,11,12,239],[1]),([0,2,3,4,12,193],[10]),([0,1,3,4,12,169],[1]),([0,1,2,3,33,239],[]),([0,1,2,3,4,80],[]),([1,2,3,33,286,326],[0,6,33]),([0,1,2,3,62,286],[0,166]),([1,2,3,4,286,326],[0]),([1,2,3,4,286,329],[0]),([0,1,2,3,33,286],[0,35]),([0,1,2,4,12,156],[]),([1,2,3,24,285,286],[477]),([0,1,2,4,156,286],[]),([0,1,2,3,39,286],[0]),([2,3,17,85,145,286],[4,11,201]),([1,2,14,17,85,286],[4,5,201]),([1,2,3,17,88,286],[11,18,201,480]),([0,1,2,3,286,369],[0]),([0,2,3,17,145,286],[124]),([0,2,3,145,286,328],[124]),([0,2,85,87,145,286],[]),([0,2,3,127,145,286],[7]),([0,2,3,85,160,286],[]),([0,2,3,85,132,145],[7]),([0,2,3,85,145,224],[1]),([0,2,85,145,224,286],[7,88,116]),([0,2,3,85,145,239],[1]),([0,1,2,4,60,85],[0,1]),([0,2,14,45,85,286],[6,7,414]),([0,2,4,45,85,224],[11,29,112,481]),([0,1,2,4,85,280],[0,1]),([0,1,85,87,111,286],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_22 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_22 = true := by decide +kernel
def h26Block5_23 : List NodeSpec := nodesWithIdentity [([0,1,2,87,88,286],[]),([0,1,2,85,90,286],[]),([1,2,3,127,285,286],[0]),([1,2,3,4,286,346],[124]),([0,1,3,4,127,132],[]),([0,1,2,14,127,286],[7]),([0,1,2,3,128,286],[0]),([0,1,2,3,4,301],[]),([0,2,4,84,85,132],[1]),([0,2,3,4,85,208],[81]),([0,1,2,14,85,132],[7]),([0,1,2,4,85,258],[1]),([0,1,2,3,88,132],[]),([0,1,2,3,4,249],[]),([0,1,2,14,17,286],[124]),([0,1,2,14,286,328],[124]),([0,1,2,14,45,85],[81]),([0,1,2,14,85,175],[81]),([0,1,2,85,130,286],[]),([0,2,3,4,85,193],[0,1]),([1,2,3,88,286,327],[0,6,88]),([0,1,2,3,137,286],[0,185]),([1,2,3,4,286,327],[0]),([1,2,3,4,286,330],[0]),([0,1,2,3,88,286],[0,87]),([0,1,3,4,85,195],[257]),([0,1,3,4,195,286],[444]),([1,2,3,145,286,326],[0,33]),([1,2,3,160,238,286],[0]),([0,1,2,3,161,286],[0]),([0,1,2,3,160,239],[]),([0,2,3,145,176,286],[1,33]),([0,2,3,121,132,145],[1]),([0,1,2,3,145,258],[1]),([0,1,2,3,123,132],[]),([1,2,3,145,286,327],[0,88]),([1,2,3,123,126,286],[0]),([0,1,2,3,166,286],[0]),([0,2,3,145,177,286],[1,88]),([0,2,3,82,145,239],[1]),([0,1,2,3,145,169],[1]),([0,1,3,111,131,286],[6,10]),([0,1,2,14,60,286],[6,81]),([1,2,3,4,175,394],[]),([0,2,3,4,175,395],[10]),([0,1,4,86,87,175],[10]),([0,1,2,3,116,175],[]),([0,1,2,3,4,515],[1]),([0,2,3,4,172,175],[]),([0,1,3,87,111,175],[7]),([0,1,3,4,87,213],[81]),([0,1,2,14,87,175],[7]),([0,1,2,4,87,280],[10]),([0,1,2,3,90,175],[]),([0,1,2,3,4,443],[]),([1,2,3,4,175,453],[]),([0,1,3,108,111,175],[10]),([0,1,3,4,108,213],[]),([0,1,2,3,175,191],[]),([0,1,2,3,4,448],[]),([1,2,3,4,175,457],[]),([0,1,2,14,109,175],[81]),([0,1,2,4,109,280],[]),([0,1,2,3,175,272],[]),([0,1,2,3,4,483],[]),([0,1,2,3,122,175],[]),([0,1,2,3,111,280],[10]),([0,1,2,3,14,213],[81]),([0,1,2,3,4,484],[]),([0,1,2,3,130,175],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_23 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_23 = true := by decide +kernel
def h26Block5_24 : List NodeSpec := nodesWithIdentity [([0,1,2,4,143,280],[]),([0,1,2,3,4,449],[]),([0,1,2,3,51,286],[0]),([1,3,44,87,111,286],[12,22,130]),([1,2,14,44,87,286],[5,22,130]),([1,2,3,44,90,286],[12,23,130,491]),([0,1,2,3,286,322],[0]),([1,2,3,172,285,286],[0]),([1,2,3,4,286,379],[124]),([0,1,3,111,172,286],[7]),([0,1,2,14,172,286],[7]),([0,1,2,3,173,286],[0]),([0,1,2,3,4,383],[]),([0,1,3,44,111,286],[124]),([0,1,3,111,286,321],[124]),([0,1,3,87,186,286],[]),([0,1,3,87,111,224],[10]),([0,1,87,111,224,286],[7,88,305]),([0,1,3,87,111,239],[10]),([0,1,2,4,61,87],[0,10]),([0,1,14,18,87,286],[7,33,414]),([0,1,4,18,87,224],[12,72,112,492]),([0,1,2,4,87,258],[0,10]),([0,1,2,14,44,286],[124]),([0,1,2,14,286,321],[124]),([0,1,2,87,174,286],[]),([0,1,2,14,18,87],[81]),([0,1,2,14,87,132],[81]),([0,1,3,4,87,169],[0,10]),([1,2,3,90,286,332],[0,33,88]),([0,1,2,3,181,286],[0,368]),([1,2,3,4,286,332],[0]),([1,2,3,4,286,333],[0]),([0,1,2,3,90,286],[0,212]),([0,2,3,4,87,197],[386]),([0,2,3,4,197,286],[462]),([1,2,3,111,286,326],[0,6]),([1,2,3,186,238,286],[0]),([0,1,2,3,187,286],[0]),([0,1,2,3,186,239],[]),([1,2,3,111,286,332],[0,88]),([0,1,2,3,190,286],[0]),([0,1,3,111,133,286],[10,88]),([0,1,3,83,111,239],[10]),([0,1,2,3,111,193],[10]),([0,1,2,14,61,286],[33,81]),([1,2,3,4,132,231],[]),([0,1,3,4,132,226],[1]),([0,1,2,3,132,150],[]),([0,1,2,3,4,514],[1]),([1,2,3,4,132,334],[]),([0,2,3,4,121,208],[]),([0,1,2,3,132,167],[]),([0,1,2,3,4,313],[]),([1,2,3,4,132,385],[]),([0,1,2,14,132,143],[81]),([0,1,2,4,143,258],[]),([0,1,2,3,132,277],[]),([0,1,2,3,4,487],[]),([0,1,2,3,14,208],[81]),([0,1,2,3,4,488],[]),([0,1,2,3,132,174],[]),([0,1,2,3,4,314],[]),([0,1,2,4,109,258],[]),([1,2,3,14,286,327],[0,6]),([0,1,2,3,276,286],[0]),([1,2,3,14,286,332],[0,33]),([0,1,2,3,271,286],[0]),([1,2,3,177,285,286],[0]),([0,2,3,4,177,288],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_24 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_24 = true := by decide +kernel
def h26Block5_25 : List NodeSpec := nodesWithIdentity [([1,2,3,133,285,286],[0]),([0,1,3,4,133,295],[]),([1,2,3,4,57,239],[]),([0,1,2,4,97,239],[1]),([0,1,2,3,155,239],[]),([0,1,2,3,4,508],[1]),([1,2,3,4,239,360],[]),([0,2,3,4,82,193],[]),([0,1,2,3,162,239],[]),([0,1,2,3,4,317],[]),([1,2,3,4,239,458],[]),([0,1,3,4,83,169],[]),([0,1,2,3,188,239],[]),([0,1,2,3,4,451],[]),([0,1,2,3,4,452],[]),([0,1,2,3,4,318],[]),([0,4,12,41,85,87],[2,11,12,13,172,178,206]),([0,2,4,12,85,254],[11,81]),([0,3,12,41,111,145],[2,11,12,13,191,195,206]),([0,2,3,12,145,247],[11,124]),([0,1,4,12,87,254],[12,81]),([0,1,3,12,111,247],[12,124]),([0,1,2,4,55,254],[0]),([0,2,3,4,41,437],[0,81,501]),([0,1,3,4,41,259],[0,81,328]),([0,1,2,4,58,254],[]),([0,1,2,3,33,247],[0]),([0,2,3,4,41,446],[0,124,503]),([0,1,3,4,41,305],[0,124,335]),([0,1,2,3,37,247],[]),([0,4,85,87,320],[5,13]),([0,3,4,85,111,320],[]),([0,2,4,14,85,320],[13]),([0,2,3,4,88,320],[]),([0,2,3,4,89,320],[]),([0,2,3,4,85,355],[81]),([0,3,4,87,145,320],[]),([0,3,111,145,320],[7,13]),([0,2,3,14,145,320],[13]),([0,2,3,4,123,320],[]),([0,2,3,4,145,348],[124]),([0,1,4,14,87,320],[13]),([0,1,3,4,90,320],[]),([0,1,3,4,94,320],[]),([0,1,3,4,87,355],[81]),([0,1,3,14,111,320],[13]),([0,1,3,4,122,320],[]),([0,1,3,4,111,348],[124]),([1,2,3,4,320,323],[]),([0,1,2,4,14,348],[124]),([0,1,2,3,14,355],[81]),([0,1,2,3,4,490],[]),([0,1,2,3,4,491],[]),([0,1,2,3,4,507],[]),([0,4,12,17,85,87],[4,5,11,16,17,148,307]),([0,3,4,12,85,164],[10,11]),([0,4,12,87,328],[4,12]),([0,2,4,12,87,328],[10]),([0,3,4,12,111,328],[4]),([0,3,4,12,120,328],[10]),([0,2,4,12,14,328],[]),([0,2,3,4,33,328],[]),([0,2,3,4,38,328],[]),([0,2,3,4,12,369],[10]),([0,4,12,44,85,87],[5,12,21,22,60,125,322]),([0,4,12,85,321],[11,22]),([0,4,33,85,87],[6,13,33,81,520,521]),([0,4,12,33,85,87],[6,13,33,36,167,178,520]),([0,4,38,85,87],[4,13,22]),([0,4,12,87,88],[4,6,10,88,522,523])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_25 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_25 = true := by decide +kernel
def h26Block5_26 : List NodeSpec := nodesWithIdentity [([0,4,12,85,87,88],[4,6,88,89,307,522,523]),([0,4,12,87,89],[4,13,22]),([0,4,12,85,90],[1,22,33,88,520,524]),([0,4,12,85,87,90],[22,33,88,125,213,520,524]),([0,4,12,85,94],[4,13,22]),([0,3,4,12,85,336],[4]),([0,12,14,85,111],[4,13,33,88]),([0,3,4,12,85,90],[1]),([0,4,12,85,90,111],[22,33,82]),([0,3,4,12,85,122],[1]),([0,3,12,88,111],[4,6,10,88,523,526]),([0,3,4,12,88,111],[10]),([0,3,12,85,88,111],[4,6,307]),([0,3,4,12,89,111],[10]),([0,2,4,12,85,323],[13]),([0,2,4,12,85,90],[1]),([0,4,12,14,85,90],[8,22,88]),([0,2,4,12,85,130],[1]),([0,2,14,33,85],[6,13,33,81,521,528]),([0,2,4,14,33,85],[81]),([0,2,12,14,33,85],[6,13,178]),([0,2,4,14,38,85],[81]),([0,2,3,4,85,326],[81,231]),([0,2,4,33,62,85],[6,13,81]),([0,2,4,12,62,85],[6,81]),([0,2,3,4,85,329],[81]),([0,2,3,4,33,85],[36,81]),([0,2,3,4,12,327],[10]),([0,3,4,12,88,137],[4,6,10]),([0,3,4,12,85,137],[6,10]),([0,2,3,4,12,330],[10]),([0,2,3,4,12,88],[10,89]),([0,3,12,45,111,145],[6,7,11,28,29,150,284]),([0,3,4,12,131,145],[10,11]),([0,3,4,12,87,324],[6]),([0,3,4,12,108,324],[10]),([0,3,12,111,324],[6,12]),([0,2,3,12,111,324],[10]),([0,2,3,12,14,324],[]),([0,2,3,4,55,324],[]),([0,2,3,4,59,324],[]),([0,2,3,4,12,368],[10]),([0,3,4,12,145,321],[6]),([0,12,14,87,145],[6,13,22,88]),([0,3,4,12,87,88],[10]),([0,4,12,87,88,145],[4,6,284]),([0,3,4,12,87,123],[10]),([0,3,12,90,145],[1,22,33,88,524,538]),([0,3,4,12,90,145],[1]),([0,3,12,87,90,145],[22,33,125]),([0,3,4,12,94,145],[1]),([0,3,12,18,111,145],[7,12,32,33,72,82,323]),([0,3,12,145,336],[11,33]),([0,3,55,111,145],[4,13,22,124,539,540]),([0,3,12,55,111,145],[4,13,22,25,157,195,539]),([0,3,59,111,145],[6,13,33]),([0,3,12,90,111,145],[22,33,82,88,213,524,538]),([0,3,12,122,145],[4,13,33]),([0,3,12,88,111,145],[4,6,88,89,284,523,526]),([0,3,12,111,123],[6,13,22]),([0,2,3,12,145,323],[13]),([0,2,3,12,90,145],[1]),([0,3,12,14,90,145],[8,33,88]),([0,2,3,12,130,145],[1]),([0,2,14,55,145],[4,13,22,124,540,542]),([0,2,3,14,55,145],[124]),([0,2,12,14,55,145],[4,13,195]),([0,2,3,14,59,145],[124]),([0,2,3,4,145,340],[124,218]),([0,2,3,55,56,145],[4,13,124])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_26 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_26 = true := by decide +kernel
def h26Block5_27 : List NodeSpec := nodesWithIdentity [([0,2,3,12,56,145],[4,124]),([0,2,3,4,145,342],[124]),([0,2,3,4,55,145],[25,124]),([0,3,4,12,137,145],[4,10]),([0,3,4,12,123,218],[10]),([0,2,3,4,12,343],[10]),([0,2,3,12,111,123],[10]),([0,3,4,12,87,189],[1,12]),([0,1,4,12,85,321],[1]),([0,3,4,12,153,321],[1]),([0,1,4,12,14,321],[]),([0,1,3,4,33,321],[]),([0,1,3,4,38,321],[]),([0,1,3,4,12,322],[1]),([0,1,4,12,87,323],[13]),([0,1,4,12,87,88],[10]),([0,4,12,14,87,88],[4,51,88]),([0,1,4,12,87,174],[10]),([0,1,14,33,87],[6,13,33,81,521,548]),([0,1,4,14,33,87],[81]),([0,1,12,14,33,87],[13,33,178]),([0,1,4,14,38,87],[81]),([0,1,3,4,87,326],[81,231]),([0,1,4,33,62,87],[13,33,81]),([0,1,4,12,62,87],[33,81]),([0,1,3,4,87,329],[81]),([0,1,3,4,33,87],[81,549]),([0,1,3,4,12,332],[1,383]),([0,3,4,12,90,181],[1,22,33]),([0,3,4,12,87,181],[1,33]),([0,1,3,4,12,333],[1]),([0,1,3,4,12,90],[1,524]),([0,3,4,12,111,176],[1,12]),([0,3,4,12,121,336],[1]),([0,1,3,12,145,336],[1]),([0,1,3,12,14,336],[]),([0,1,3,4,55,336],[]),([0,1,3,4,59,336],[]),([0,1,3,4,12,337],[1]),([0,1,3,12,111,323],[13]),([0,1,3,12,88,111],[10]),([0,3,12,14,88,111],[6,51,88]),([0,1,3,12,111,174],[10]),([0,1,14,55,111],[4,13,22,124,540,556]),([0,1,3,14,55,111],[124]),([0,1,12,14,55,111],[13,22,195]),([0,1,3,14,59,111],[124]),([0,1,3,4,111,340],[124,218]),([0,1,3,55,56,111],[13,22,124]),([0,1,3,12,56,111],[22,124]),([0,1,3,4,111,342],[124]),([0,1,3,4,55,111],[124,557]),([0,3,4,12,111,181],[1,22]),([0,1,3,4,12,341],[1]),([0,2,3,4,12,424],[10]),([0,1,3,4,12,365],[1]),([0,1,2,4,55,323],[]),([0,1,2,3,33,323],[]),([0,1,2,3,4,425],[]),([0,1,3,4,12,137],[0,1]),([0,1,2,3,4,19],[0]),([0,3,4,12,88,90],[4,89,213,564]),([0,1,3,4,12,276],[0,1]),([0,2,3,4,12,181],[0,1]),([0,2,3,4,12,271],[0,1]),([0,1,2,4,14,340],[124,218]),([0,1,2,14,55,56],[4,22,124]),([0,1,2,3,14,56],[0,81]),([0,1,2,14,33,55],[4,178,195,568]),([0,1,2,4,14,55],[124,566])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_27 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_27 = true := by decide +kernel
def h26Block5_28 : List NodeSpec := nodesWithIdentity [([0,1,2,3,14,78],[0,81]),([0,1,2,3,14,326],[81,231]),([0,1,2,14,33,62],[6,33,81]),([0,1,2,4,14,62],[0,81]),([0,1,2,4,14,71],[0,81]),([0,1,2,3,14,33],[81,569]),([1,2,3,4,19,344],[]),([1,2,3,4,345],[]),([0,1,2,3,4,345],[]),([1,2,3,4,19,345],[0]),([0,1,2,3,4,181],[]),([0,2,3,4,19,181],[0,368]),([0,1,2,3,4,137],[]),([0,1,3,4,19,137],[0,185]),([0,1,2,3,4,62],[]),([0,1,2,4,19,62],[0,166]),([0,1,2,3,4,56],[]),([0,1,2,3,19,56],[0,156]),([1,2,3,4,12,345],[575]),([1,2,3,4,14,345],[576]),([1,2,3,4,22,339],[579]),([0,2,3,4,55,189],[0]),([0,1,3,4,55,164],[0]),([0,1,2,3,55,99],[]),([0,1,2,3,4,349],[]),([1,2,3,4,55,345],[]),([0,2,3,4,55,181],[0]),([0,1,3,4,55,137],[0]),([0,1,2,4,55,62],[0]),([0,1,2,3,4,350],[]),([0,1,2,3,33,56],[0]),([0,1,2,3,4,492],[]),([0,1,2,3,4,351],[]),([1,2,3,4,24,325],[592]),([0,2,3,4,33,176],[0]),([0,1,3,4,33,131],[0]),([0,1,2,4,33,156],[]),([0,1,2,3,4,354],[]),([1,2,3,4,33,345],[]),([0,2,3,4,33,181],[0]),([0,1,3,4,33,137],[0]),([0,1,2,3,4,356],[]),([0,1,2,3,4,493],[]),([0,1,2,3,4,357],[]),([0,2,14,17,85,145],[4,5,11,17,85,198,201]),([0,2,3,39,85,145],[11,124]),([0,1,4,85,87,164],[5,10]),([0,1,2,14,39,85],[5,124]),([0,1,2,3,39,88],[0]),([0,2,4,87,145,328],[]),([0,2,3,111,145,328],[4]),([0,2,3,124,145,328],[124]),([0,2,3,4,160,328],[]),([0,2,3,4,145,347],[124]),([0,2,14,145,328],[4,7]),([0,2,4,14,145,328],[124]),([0,1,4,87,111,328],[4]),([0,1,4,87,120,328],[10]),([0,1,2,4,90,328],[]),([0,1,2,4,94,328],[]),([0,1,2,4,87,369],[10]),([1,2,3,4,328,410],[10]),([0,2,3,4,328,411],[]),([0,1,3,110,111,328],[10]),([0,1,2,4,149,328],[]),([0,1,2,3,4,528],[0]),([1,2,3,4,328,336],[]),([0,1,3,4,111,347],[124]),([0,1,2,14,111,328],[4]),([0,1,2,3,111,369],[10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_28 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_28 = true := by decide +kernel
def h26Block5_29 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,455],[]),([0,2,3,4,328,436],[]),([0,1,3,4,120,347],[]),([0,1,2,4,185,328],[]),([0,1,2,3,4,520],[]),([0,2,3,4,328,446],[]),([0,1,2,14,124,328],[124]),([0,1,2,4,311,328],[]),([0,1,2,3,124,369],[]),([0,1,2,3,4,527],[]),([0,1,2,4,14,347],[124]),([0,1,2,3,4,456],[]),([0,1,2,4,130,328],[]),([0,1,2,3,319,369],[]),([0,1,2,3,4,512],[]),([0,2,14,45,85,145],[6,7,11,29,86,181,285]),([0,2,4,60,85,145],[11,81]),([0,2,4,85,87,324],[6]),([0,2,4,85,109,324],[81]),([0,2,3,85,111,324],[]),([0,2,3,4,127,324],[]),([0,2,3,4,85,353],[81]),([0,2,14,85,324],[5,6]),([0,2,3,14,85,324],[81]),([0,2,4,85,145,321],[6]),([0,85,87,111,145],[4,6,22,33]),([0,2,4,33,85,87],[81]),([0,4,33,85,87,145],[6,13,285]),([0,2,4,85,87,160],[81]),([0,2,85,90,145],[1,22,33,88,524,612]),([0,2,4,85,90,145],[1]),([0,2,85,87,90,145],[22,88,125]),([0,2,4,85,94,145],[1]),([0,2,3,85,145,336],[4]),([0,2,3,55,111,145],[124]),([0,3,55,85,111,145],[4,13,201]),([0,2,3,111,127,145],[124]),([0,2,3,85,90,145],[1]),([0,2,85,90,111,145],[33,82,88]),([0,2,3,85,122,145],[1]),([0,2,14,55,85,145],[4,13,22,25,178,201,542]),([0,2,3,56,85,145],[13,124]),([0,2,3,127,145,319],[124]),([0,2,3,4,145,346],[124]),([0,2,14,127,145],[4,6,33]),([0,2,4,14,127,145],[124]),([0,2,14,33,85,145],[6,13,33,36,285,521,528]),([0,2,4,62,85,145],[13,81]),([0,2,4,85,160,284],[81]),([0,2,3,4,85,352],[81]),([0,2,14,85,160],[4,6,22]),([0,2,3,14,85,160],[81]),([0,2,14,85,145,224],[5,7,8,88,90,112,431]),([0,2,85,145,323],[11,88]),([0,2,14,85,90,145],[8,22,33,88,214,524,612]),([0,2,85,130,145],[13,88]),([0,2,4,85,87,189],[1,5]),([0,2,4,85,153,321],[1]),([0,1,4,85,111,321],[]),([0,1,2,4,88,321],[]),([0,1,2,4,89,321],[]),([0,1,2,4,85,322],[1]),([0,1,4,85,87,336],[4]),([0,1,4,33,85,87],[81]),([0,4,33,85,87,111],[13,33,97]),([0,1,4,85,87,186],[81]),([0,1,87,88,111],[4,6,10,88,523,619]),([0,1,4,87,88,111],[10]),([0,1,85,87,88,111],[4,88,307]),([0,1,4,87,89,111],[10])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_29 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_29 = true := by decide +kernel
def h26Block5_30 : List NodeSpec := nodesWithIdentity [([0,1,2,4,87,327],[10]),([0,1,4,87,88,137],[4,10,88]),([0,1,4,85,87,137],[10,88]),([0,1,2,4,87,330],[10]),([0,1,2,4,87,88],[10,620]),([0,1,2,4,85,332],[1,383]),([0,2,4,85,90,181],[1,22,88]),([0,2,4,85,87,181],[1,88]),([0,1,2,4,85,333],[1]),([0,1,2,4,85,90],[1,524]),([0,2,4,84,85,336],[1]),([0,2,3,4,85,398],[81]),([0,1,2,14,85,336],[4]),([0,1,2,4,85,337],[1]),([0,1,2,3,88,336],[]),([0,1,2,3,4,399],[]),([0,1,2,4,62,85],[0,1]),([0,2,14,33,85,111],[6,33,97]),([0,2,4,33,85,90],[13,36,214,626]),([0,1,2,4,85,187],[0,1]),([0,1,2,3,56,111],[0,10]),([0,1,14,55,85,111],[4,22,201]),([0,1,3,55,88,111],[13,157,201,627]),([0,1,2,3,111,128],[0,10]),([0,1,2,85,111,323],[]),([0,1,2,14,33,85],[81]),([0,1,2,14,85,186],[81]),([0,1,2,14,55,111],[124]),([0,1,2,14,111,127],[124]),([0,2,3,4,85,181],[0,1]),([0,2,3,4,85,190],[0,1]),([0,1,2,3,111,327],[10]),([0,1,3,88,111,137],[6,10,88]),([0,1,3,4,111,137],[0,10]),([0,1,3,4,111,138],[0,10]),([0,1,2,3,88,111],[10,628]),([1,2,3,4,85,345],[575]),([1,2,3,4,111,345],[630]),([0,1,2,14,56,85],[22,124]),([0,1,2,3,56,88],[0]),([0,2,3,4,127,146],[]),([0,1,3,4,113,127],[0]),([0,1,2,4,127,236],[]),([0,1,2,3,4,513],[0]),([1,2,3,4,293,346],[]),([0,2,3,4,127,184],[]),([0,1,2,4,127,245],[]),([0,1,2,3,4,363],[]),([0,2,3,4,127,404],[]),([0,1,2,14,127,319],[124]),([0,1,2,4,127,376],[]),([0,1,2,3,128,319],[]),([0,1,2,3,4,530],[]),([0,1,2,4,14,346],[124]),([0,1,2,3,4,459],[]),([0,1,2,4,127,323],[]),([0,1,2,3,4,364],[]),([0,2,4,14,85,177],[1,5]),([0,1,2,4,85,365],[1]),([0,2,4,14,85,181],[1,22]),([0,1,2,4,85,362],[1]),([1,2,3,4,26,359],[639]),([0,2,3,4,88,177],[0]),([0,1,3,4,88,195],[]),([0,1,2,4,60,88],[0]),([1,2,3,4,7,327],[]),([1,2,3,4,9,327],[]),([1,2,3,4,218,327],[]),([1,2,3,4,238,327],[]),([1,2,3,4,293,327],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_30 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_30 = true := by decide +kernel
def h26Block5_31 : List NodeSpec := nodesWithIdentity [([0,2,3,4,82,327],[]),([0,1,2,4,109,327],[]),([0,1,2,3,124,327],[]),([0,1,2,3,4,367],[]),([1,2,3,4,98,327],[]),([1,2,3,4,88,345],[]),([0,2,3,4,88,181],[0]),([0,1,2,4,62,88],[0]),([0,1,2,3,4,370],[]),([1,2,3,4,105,327],[]),([0,2,4,84,85,327],[1]),([0,1,2,3,4,460],[]),([0,1,2,3,4,371],[]),([0,1,3,111,131,145],[7,10]),([0,1,2,14,60,145],[7,81]),([1,2,3,4,324,394],[10]),([0,2,3,4,324,395],[]),([0,1,4,86,87,324],[10]),([0,1,2,3,116,324],[]),([0,1,2,3,4,535],[0]),([1,2,3,4,321,324],[]),([0,1,3,87,111,324],[6]),([0,1,3,4,87,353],[81]),([0,1,2,14,87,324],[6]),([0,1,2,4,87,368],[10]),([0,1,2,3,90,324],[]),([0,1,2,3,4,463],[]),([0,2,3,4,324,435],[]),([0,1,3,108,111,324],[10]),([0,1,3,4,108,353],[]),([0,1,2,3,191,324],[]),([0,1,2,3,4,521],[]),([0,2,3,4,324,437],[]),([0,1,2,14,109,324],[81]),([0,1,2,4,109,368],[]),([0,1,2,3,272,324],[]),([0,1,2,3,4,529],[]),([0,1,2,3,122,324],[]),([0,1,2,3,111,368],[10]),([0,1,2,3,14,353],[81]),([0,1,2,3,4,464],[]),([0,1,2,3,130,324],[]),([0,1,2,4,284,368],[]),([0,1,2,3,4,497],[]),([0,2,3,144,145,321],[1]),([0,2,3,4,145,380],[124]),([0,1,3,111,145,321],[6]),([0,1,2,14,145,321],[6]),([0,1,2,3,145,322],[1]),([0,1,2,3,4,381],[]),([0,1,2,3,56,145],[0,1]),([0,3,55,87,111,145],[13,22,130]),([0,2,14,55,87,145],[4,22,130]),([0,2,3,55,90,145],[13,25,130,650]),([0,1,2,3,145,173],[0,1]),([0,1,3,87,145,336],[]),([0,1,3,55,111,145],[124]),([0,1,3,111,145,172],[124]),([0,1,3,87,88,111],[10]),([0,1,87,88,111,145],[6,88,284]),([0,1,3,87,111,123],[10]),([0,1,2,4,62,87],[0,10]),([0,1,14,33,87,145],[6,33,285]),([0,1,4,33,87,88],[13,167,186,651]),([0,1,2,4,87,161],[0,10]),([0,1,2,87,145,323],[]),([0,1,2,14,55,145],[124]),([0,1,2,14,145,172],[124]),([0,1,2,14,33,87],[81]),([0,1,2,14,87,160],[81])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_31 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_31 = true := by decide +kernel
def h26Block5_32 : List NodeSpec := nodesWithIdentity [([0,1,3,4,87,137],[0,10]),([0,1,3,4,87,166],[0,10]),([0,1,2,3,145,332],[1,383]),([0,2,3,90,145,181],[1,33,88]),([0,2,3,4,145,181],[0,1]),([0,2,3,4,145,182],[0,1]),([0,1,2,3,90,145],[1,524]),([1,2,3,4,87,345],[630]),([1,2,3,4,145,345],[575]),([0,2,3,111,145,176],[1,7]),([0,2,3,121,145,336],[1]),([0,1,2,3,123,336],[]),([0,1,2,3,145,337],[1]),([0,2,3,111,145,181],[1,88]),([0,1,2,3,145,341],[1]),([0,1,3,111,137,145],[10,88]),([0,1,3,111,123,218],[10]),([0,1,2,3,111,343],[10]),([0,1,2,14,62,145],[33,81]),([0,2,3,4,104,160],[]),([0,1,3,4,95,160],[0]),([0,1,2,3,160,290],[]),([0,1,2,3,4,498],[0]),([1,2,3,4,238,352],[]),([0,2,3,4,160,183],[]),([0,1,2,3,160,300],[]),([0,1,2,3,4,374],[]),([0,2,3,4,160,386],[]),([0,1,2,14,160,284],[81]),([0,1,2,4,161,284],[]),([0,1,2,3,160,366],[]),([0,1,2,3,4,531],[]),([0,1,2,3,14,352],[81]),([0,1,2,3,4,466],[]),([0,1,2,3,160,323],[]),([0,1,2,3,4,375],[]),([0,2,3,14,145,177],[1,7]),([0,1,2,3,145,365],[1]),([0,2,3,14,145,181],[1,33]),([0,1,2,3,145,362],[1]),([1,2,3,4,147,327],[]),([0,2,3,144,145,327],[1]),([0,2,3,4,52,123],[]),([0,1,2,4,123,227],[0]),([0,1,2,3,123,294],[]),([0,1,2,3,4,467],[0]),([1,2,3,4,126,343],[]),([0,2,3,4,123,261],[]),([0,1,2,3,123,298],[]),([0,1,2,3,4,377],[]),([0,2,3,4,123,489],[]),([0,1,3,4,166,218],[]),([0,1,2,3,123,338],[]),([0,1,2,3,4,522],[]),([0,1,2,3,4,468],[]),([0,1,2,3,4,378],[]),([0,1,14,44,87,111],[5,12,22,60,103,130,371]),([0,1,3,51,87,111],[12,124]),([0,1,2,14,51,87],[5,124]),([0,1,2,3,51,90],[0]),([1,2,3,4,287,321],[1]),([0,1,3,4,235,321],[]),([0,1,2,4,114,321],[]),([0,1,2,3,4,536],[0]),([0,2,3,4,153,380],[]),([0,1,3,4,244,321],[]),([0,1,2,4,141,321],[]),([0,1,2,3,4,523],[]),([0,1,3,111,170,321],[124]),([0,1,3,4,305,321],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_32 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_32 = true := by decide +kernel
def h26Block5_33 : List NodeSpec := nodesWithIdentity [([0,1,2,14,170,321],[124]),([0,1,2,4,315,321],[]),([0,1,2,3,170,322],[]),([0,1,2,3,4,538],[]),([0,1,3,4,111,380],[124]),([0,1,2,4,14,380],[124]),([0,1,2,3,4,382],[]),([0,1,3,4,186,321],[]),([0,1,14,111,321],[7,22]),([0,1,4,14,111,321],[124]),([0,1,2,4,174,321],[]),([0,1,2,3,4,516],[]),([0,1,14,55,87,111],[4,13,22,130,157,178,556]),([0,1,3,56,87,111],[13,124]),([0,1,2,14,56,87],[4,124]),([0,1,2,3,56,90],[0]),([0,2,3,4,146,172],[0]),([0,1,3,4,113,172],[]),([0,1,2,4,172,236],[]),([0,1,2,3,4,517],[0]),([1,2,3,4,293,379],[]),([0,1,3,4,140,172],[]),([0,1,2,4,172,245],[]),([0,1,2,3,4,471],[]),([0,1,3,111,172,319],[124]),([0,1,3,4,172,372],[]),([0,1,2,14,172,319],[124]),([0,1,2,4,172,376],[]),([0,1,2,3,173,319],[]),([0,1,2,3,4,539],[]),([0,1,3,4,111,379],[124]),([0,1,2,4,14,379],[124]),([0,1,2,3,4,384],[]),([0,1,3,4,172,336],[]),([0,1,14,111,172],[6,22]),([0,1,4,14,111,172],[124]),([0,1,2,4,172,323],[]),([0,1,2,3,4,472],[]),([0,1,14,18,87,111],[7,12,33,72,97,292,364]),([0,1,4,61,87,111],[12,81]),([0,1,4,87,143,336],[81]),([0,1,3,4,87,398],[81]),([0,1,14,87,336],[5,33]),([0,1,3,14,87,336],[81]),([0,1,14,33,87,111],[6,13,33,97,167,521,548]),([0,1,4,62,87,111],[13,81]),([0,1,4,87,186,284],[81]),([0,1,3,4,87,397],[81]),([0,1,14,87,186],[4,33]),([0,1,3,14,87,186],[81]),([0,1,14,87,111,224],[5,7,51,88,112,293,452]),([0,1,87,111,323],[12,88]),([0,1,14,87,88,111],[4,6,51,88,186,523,619]),([0,1,87,111,174],[13,88]),([0,1,4,14,87,133],[5,10]),([0,1,2,4,87,424],[10]),([0,1,4,14,87,137],[4,10]),([0,1,2,4,87,423],[10]),([1,2,3,4,28,331],[682]),([0,2,3,4,90,197],[]),([0,1,3,4,90,133],[0]),([0,1,2,4,61,90],[0]),([0,1,2,3,4,387],[]),([1,2,3,4,90,345],[]),([0,1,3,4,90,137],[0]),([0,1,2,4,62,90],[0]),([0,1,2,3,4,388],[]),([0,1,2,3,4,389],[]),([0,1,2,3,4,390],[]),([0,1,2,14,61,111],[7,81])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_33 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_33 = true := by decide +kernel
def h26Block5_34 : List NodeSpec := nodesWithIdentity [([1,2,3,4,231,336],[1]),([0,1,3,4,226,336],[]),([0,1,2,3,150,336],[]),([0,1,2,3,4,532],[0]),([0,2,3,4,121,398],[]),([0,1,3,4,243,336],[]),([0,1,2,3,167,336],[]),([0,1,2,3,4,524],[]),([0,1,3,4,259,336],[]),([0,1,2,14,143,336],[81]),([0,1,2,4,143,337],[]),([0,1,2,3,277,336],[]),([0,1,2,3,4,540],[]),([0,1,2,3,14,398],[81]),([0,1,2,3,4,400],[]),([0,1,2,3,174,336],[]),([0,1,2,3,4,501],[]),([0,1,2,14,62,111],[6,81]),([0,2,3,4,104,186],[0]),([0,1,3,4,95,186],[]),([0,1,2,3,186,290],[]),([0,1,2,3,4,502],[0]),([1,2,3,4,238,397],[]),([0,1,3,4,139,186],[]),([0,1,2,3,186,300],[]),([0,1,2,3,4,473],[]),([0,1,3,4,186,358],[]),([0,1,2,14,186,284],[81]),([0,1,2,4,187,284],[]),([0,1,2,3,186,366],[]),([0,1,2,3,4,541],[]),([0,1,2,3,14,397],[81]),([0,1,2,3,4,402],[]),([0,1,2,3,186,323],[]),([0,1,2,3,4,474],[]),([0,1,3,14,111,133],[7,10]),([0,1,2,3,111,424],[10]),([0,1,3,14,111,137],[6,10]),([0,1,2,3,111,423],[10]),([0,1,2,3,4,405],[]),([0,1,2,3,4,406],[]),([0,2,3,4,115,177],[]),([0,1,2,13,14,177],[81]),([0,1,3,4,117,133],[]),([0,1,2,13,14,133],[81]),([0,1,2,3,4,426],[]),([0,1,2,3,4,475],[]),([1,2,3,4,237,327],[]),([0,1,2,13,14,327],[81]),([1,2,3,4,7,423],[]),([1,2,3,4,126,423],[]),([0,1,2,3,4,428],[]),([0,1,2,3,4,476],[]),([0,1,2,3,4,429],[]),([0,1,2,3,4,430],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test5_34 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Block5_34 = true := by decide +kernel
def h26Nodes5 : List NodeSpec := h26Block5_0 ++ h26Block5_1 ++ h26Block5_2 ++ h26Block5_3 ++ h26Block5_4 ++ h26Block5_5 ++ h26Block5_6 ++ h26Block5_7 ++ h26Block5_8 ++ h26Block5_9 ++ h26Block5_10 ++ h26Block5_11 ++ h26Block5_12 ++ h26Block5_13 ++ h26Block5_14 ++ h26Block5_15 ++ h26Block5_16 ++ h26Block5_17 ++ h26Block5_18 ++ h26Block5_19 ++ h26Block5_20 ++ h26Block5_21 ++ h26Block5_22 ++ h26Block5_23 ++ h26Block5_24 ++ h26Block5_25 ++ h26Block5_26 ++ h26Block5_27 ++ h26Block5_28 ++ h26Block5_29 ++ h26Block5_30 ++ h26Block5_31 ++ h26Block5_32 ++ h26Block5_33 ++ h26Block5_34
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Check5 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket4 5 h26Nodes5 = true := by
  unfold h26Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h26Test5_0,h26Test5_1⟩,h26Test5_2⟩,h26Test5_3⟩,h26Test5_4⟩,h26Test5_5⟩,h26Test5_6⟩,h26Test5_7⟩,h26Test5_8⟩,h26Test5_9⟩,h26Test5_10⟩,h26Test5_11⟩,h26Test5_12⟩,h26Test5_13⟩,h26Test5_14⟩,h26Test5_15⟩,h26Test5_16⟩,h26Test5_17⟩,h26Test5_18⟩,h26Test5_19⟩,h26Test5_20⟩,h26Test5_21⟩,h26Test5_22⟩,h26Test5_23⟩,h26Test5_24⟩,h26Test5_25⟩,h26Test5_26⟩,h26Test5_27⟩,h26Test5_28⟩,h26Test5_29⟩,h26Test5_30⟩,h26Test5_31⟩,h26Test5_32⟩,h26Test5_33⟩,h26Test5_34⟩
def h26Bucket5 : BT (List (List Nat)) := buildBucketsBT h26W h26Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G 5 xs.toFinset) h26Bucket5 := buildBucketsBT_sound (by decide) h26Pairs h26WOk h26PoolsOk h26AutosOk h26Bucket4Ok h26Check5
def h26Block6_0 : List NodeSpec := nodesWithIdentity [([3,4,6,10,12],[0,1,2,3,10,11,12,13,14,19,26]),([2,3,4,6,10,85],[0,1,2,4,11,12,37,38,39]),([2,3,4,6,10,145],[0,1,2,6,11,12,41,42,43]),([1,3,4,6,10,87],[0,10,11,12,19,22,38,45,46]),([1,3,4,6,10,111],[0,10,11,12,19,33,42,48,49]),([1,2,3,4,6,10,14],[2,8,11,12,19,38,51]),([1,2,3,4,10,17],[4,5,10,11,16,18,52,53]),([1,2,3,4,6,10,17],[4,5,11,16,17,19,53]),([1,2,3,4,10,43],[0,10,11,12,53,55,56,57]),([1,2,3,4,6,44],[1,5,12,21,22,23,38,58]),([1,2,3,4,6,10,44],[2,5,12,21,22,38,60]),([1,2,3,4,6,54],[0,1,11,12,38,61,62,63]),([1,2,3,4,10,45],[6,7,10,11,28,30,64,65]),([1,2,3,4,6,10,45],[6,7,11,19,28,29,65]),([1,2,3,4,10,47],[0,10,11,12,65,67,68,69]),([1,2,3,4,6,18],[1,7,12,32,33,34,42,70]),([1,2,3,4,6,10,18],[2,7,12,32,33,42,72]),([1,2,3,4,6,32],[0,1,11,12,42,73,74,75]),([2,3,4,6,12,220],[0,1,5,11,13,26,76,77,78]),([2,4,6,85,220],[0,1,4,5,11,39,76,80,81,83,85]),([2,3,4,6,145,220],[0,1,5,6,11,43,76,92,93]),([1,2,4,6,87,220],[0,5,11,22,46,77,81,85,95]),([1,2,3,4,6,111,220],[5,11,76,77,82,85,97]),([1,2,3,4,41,220],[11,12,13,26,81,98,99]),([1,2,3,4,6,41,220],[2,11,12,13,85,99]),([1,2,3,4,125,220],[0,5,11,77,81,100,101,102]),([1,2,3,4,6,44,220],[5,12,21,22,58,76,103]),([1,2,3,4,6,134],[0,1,5,11,58,104]),([1,2,4,6,14,220],[0,5,9,11,81,85,88,93,105]),([1,2,3,4,45,220],[6,7,11,30,81,86,93,107]),([1,2,3,4,6,45,220],[6,7,11,29,85,86,93]),([1,2,3,4,47,220],[0,5,11,69,81,93,109,110]),([1,2,3,4,6,224],[1,5,7,88,90,91,93,111]),([1,2,3,4,6,220,224],[5,7,76,88,90,93,112]),([1,2,3,4,6,225],[0,1,5,11,93,113,114,115]),([2,3,4,6,12,286],[0,1,7,11,13,26,116,117,118]),([2,3,4,6,85,286],[0,1,4,7,11,39,116,120,121]),([2,3,6,145,286],[0,1,6,7,11,43,116,123,124,126,128]),([1,2,3,4,6,87,286],[7,11,116,117,125,128,130]),([1,2,3,6,111,286],[0,7,11,33,49,117,124,128,131]),([1,2,3,4,41,286],[11,12,13,26,124,133,134]),([1,2,3,4,6,41,286],[2,11,12,13,128,134]),([1,2,3,4,125,286],[0,7,11,102,117,124,135,136]),([1,2,3,4,6,18,286],[7,12,32,33,70,116,137]),([1,2,3,4,6,132],[0,1,7,11,70,138]),([1,2,3,6,14,286],[0,7,9,11,88,120,124,128,139]),([1,2,3,4,17,286],[4,5,11,18,120,124,129,141]),([1,2,3,4,6,17,286],[4,5,11,17,120,128,129]),([1,2,3,4,43,286],[0,7,11,57,120,124,143,144]),([1,2,3,4,6,224,286],[5,7,88,90,111,116,145]),([1,2,3,4,6,239],[0,1,7,11,111,146]),([0,3,4,6,12,87],[1,10,11,13,19,22,78,125,147]),([0,3,4,6,12,111],[1,10,11,13,19,33,82,118,149]),([0,2,3,4,6,12,14],[9,11,13,19,26,51,78]),([0,2,3,4,12,17],[4,5,10,11,16,17,151,152]),([0,2,3,4,6,12,17],[4,5,11,16,18,19,152]),([0,2,3,4,12,43],[1,10,11,13,56,152,153,154]),([0,2,3,4,6,55],[0,4,13,22,24,25,78,155]),([0,2,3,4,6,12,55],[4,13,22,24,26,78,157]),([0,2,3,4,6,59],[0,1,11,13,78,158,159,160]),([0,2,3,4,12,45],[6,7,10,11,28,29,161,162]),([0,2,3,4,6,12,45],[6,7,11,19,28,30,162]),([0,2,3,4,12,47],[1,10,11,13,68,162,163,164]),([0,2,3,4,6,33],[0,6,13,33,35,36,118,165]),([0,2,3,4,6,12,33],[6,13,26,33,35,118,167]),([0,2,3,4,6,38],[0,1,11,13,118,168,169,170]),([0,2,4,6,85,87],[1,4,11,22,37,81,85,125,171]),([0,2,3,4,6,85,111],[4,11,37,39,49,85,97]),([0,2,3,4,41,85],[2,11,12,13,81,173,174]),([0,2,3,4,6,41,85],[11,12,13,26,85,174])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_0 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_0 = true := by decide +kernel
def h26Block6_1 : List NodeSpec := nodesWithIdentity [([0,2,3,4,85,125],[1,4,11,81,101,175,176,177]),([0,2,3,4,6,55,85],[4,13,22,24,39,155,178]),([0,2,3,4,6,127],[0,1,4,11,155,179]),([0,2,4,6,14,85],[1,4,8,11,81,85,88,121,180]),([0,2,3,4,45,85],[6,7,11,29,81,86,121,182]),([0,2,3,4,6,45,85],[6,7,11,30,85,86,121]),([0,2,3,4,47,85],[1,4,11,81,110,121,164,183]),([0,2,3,4,6,88],[0,4,6,87,88,89,121,184]),([0,2,3,4,6,85,88],[4,6,39,87,88,121,186]),([0,2,3,4,6,89],[0,1,4,11,121,187,188,189]),([0,2,3,4,6,87,145],[6,11,41,43,46,128,130]),([0,2,3,6,111,145],[1,6,11,33,41,82,124,128,190]),([0,2,3,4,41,145],[2,11,12,13,124,192,193]),([0,2,3,4,6,41,145],[11,12,13,26,128,193]),([0,2,3,4,125,145],[1,6,11,41,124,136,177,194]),([0,2,3,4,6,33,145],[6,13,33,35,43,165,195]),([0,2,3,4,6,160],[0,1,6,11,165,196]),([0,2,3,6,14,145],[1,6,8,11,88,92,124,128,197]),([0,2,3,4,17,145],[4,5,11,17,92,124,129,199]),([0,2,3,4,6,17,145],[4,5,11,18,92,128,129]),([0,2,3,4,43,145],[1,6,11,92,124,144,154,200]),([0,2,3,4,6,88,145],[4,6,43,87,88,184,201]),([0,2,3,4,6,123],[0,1,6,11,184,202]),([0,1,2,3,4,6,44],[1,22,23]),([1,2,3,4,6,44,87],[0,5,12,21,22,58,125]),([0,1,2,3,4,6,321],[1,22,23]),([0,1,2,3,4,6,55],[0,22,24,25]),([0,2,3,4,6,55,87],[1,4,13,22,24,46,155]),([0,1,2,3,4,6,172],[0,22,25]),([0,1,3,4,6,87,111],[22,33,85,97,128,130,204]),([0,1,3,4,41,87],[11,12,13,45,81,147,206]),([0,1,2,3,4,41,87],[11,81,206]),([0,1,3,4,6,41,87],[10,11,12,13,85,147]),([0,1,2,3,4,87,125],[11,19,81]),([0,1,2,4,6,14,87],[19,22,51,88,128,130,208]),([0,1,2,4,17,87],[4,5,10,11,16,85,209,210]),([0,1,2,3,4,17,87],[10,11,16,85]),([0,1,2,4,6,17,87],[4,5,11,16,19,81,209]),([0,1,2,3,4,43,87],[10,11,56,85]),([0,1,2,3,4,45,87],[10,22,28,29,30,81,128]),([0,1,2,3,4,47,87],[10,11,22,68,69,81,128,164]),([0,1,2,3,4,6,90],[0,1,11,130,212,213,214]),([0,1,2,3,4,6,94],[0,1,11,22,130,215,216,217]),([0,1,2,3,4,22],[16,124,219]),([0,1,2,3,4,6,22],[22,128,219]),([0,1,2,3,4,22,87],[11,16,130]),([0,1,2,3,4,87,101],[221]),([0,1,2,3,4,6,50],[222]),([0,1,2,3,4,6,18],[1,33,34]),([1,2,3,4,6,18,111],[0,7,12,32,33,70,82]),([0,1,2,3,4,6,336],[1,33,34]),([0,1,2,3,4,6,33],[0,33,35,36]),([0,2,3,4,6,33,111],[1,6,13,33,35,49,165]),([0,1,2,3,4,6,186],[0,33,36]),([0,1,3,4,41,111],[11,12,13,48,124,149,206]),([0,1,2,3,4,41,111],[11,124,206]),([0,1,3,4,6,41,111],[10,11,12,13,128,149]),([0,1,2,3,4,111,125],[11,19,124]),([0,1,2,3,6,14,111],[19,33,51,85,88,97,224]),([0,1,2,3,4,17,111],[10,16,17,18,33,85,124]),([0,1,2,3,4,43,111],[10,11,33,56,57,85,124,154]),([0,1,2,3,4,6,122],[0,1,11,33,97,226,227,228]),([0,1,2,3,45,111],[6,7,10,11,28,128,229,230]),([0,1,2,3,4,45,111],[10,11,28,128]),([0,1,2,3,6,45,111],[6,7,11,19,28,124,229]),([0,1,2,3,4,47,111],[10,11,68,128]),([0,1,2,3,4,24],[32,81,233]),([0,1,2,3,4,6,24],[32,33,85]),([0,1,2,3,4,24,111],[11,97,233]),([0,1,2,3,4,111,112],[234])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_1 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_1 = true := by decide +kernel
def h26Block6_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,6,49],[235]),([0,1,2,3,4,13,41],[2,26,81,124,206]),([0,1,2,3,4,14,41],[2,26,81,88,124,206]),([0,1,2,3,4,15,41],[2,26,81,124,206]),([0,1,2,3,4,16,41],[2,26,81,124,206]),([0,1,2,3,4,41,253],[2,11,12,13,26,81,206]),([0,1,2,3,4,22,41],[81]),([0,1,2,3,4,41,129],[81]),([0,1,2,3,4,254],[0,1,10,11,12,13,124,236,237,238]),([0,1,2,3,4,41,254],[2,11,12,13,26,81,206]),([0,1,2,3,4,41,246],[2,11,12,13,26,124,206]),([0,1,2,3,4,24,41],[124]),([0,1,2,3,4,41,163],[124]),([0,1,2,3,4,247],[0,1,10,11,12,13,81,239,240,241]),([0,1,2,3,4,41,247],[2,11,12,13,26,124,206]),([0,1,2,3,4,17,41],[10,12,81,85,206,242]),([0,1,2,3,4,41,42],[10,12,81,206]),([0,1,2,3,4,6,254],[0,1,10,11,12,13,81,236]),([0,1,2,3,4,41,45],[10,12,124,128,161,206]),([0,1,2,3,4,41,46],[10,12,124,206]),([0,1,2,3,4,6,247],[0,1,10,11,12,13,124,239]),([0,1,2,3,4,41],[11,26,81,124]),([0,1,2,3,4,14,125],[11,19,81,88,101,102,124,177]),([0,1,2,3,4,199],[0,1,10,11,16,124,243]),([0,1,2,3,4,210],[0,1,10,11,28,81,244]),([0,1,2,3,4,6,224],[1,88,91]),([1,2,3,4,6,14,224],[0,5,7,8,88,90,111]),([0,1,2,3,4,6,323],[1,9,88]),([0,1,2,3,4,6,88],[0,87,88,89]),([0,2,3,4,6,14,88],[1,4,6,9,87,88,184]),([0,1,2,3,4,6,174],[0,8,88,246]),([0,1,2,3,4,6,130],[0,1,11,51,88,247,248,249]),([0,1,2,4,14,17],[4,5,11,85,124,129,250,251]),([0,1,2,3,4,14,17],[11,85,124]),([0,1,2,4,6,14,17],[4,5,11,81,128,129,250]),([0,1,2,3,4,14,43],[11,85,124]),([0,1,2,3,14,45],[6,7,11,81,86,128,253,254]),([0,1,2,3,4,14,45],[11,81,86,128]),([0,1,2,3,6,14,45],[6,7,11,85,86,124,253]),([0,1,2,3,4,14,47],[11,81,110,128]),([0,1,2,3,4,26],[10,129,255]),([0,1,2,3,4,6,26],[19,88]),([0,1,2,3,4,14,26],[11,51,255]),([0,1,2,3,4,14,27],[258]),([0,1,2,3,4,6,48],[259]),([0,1,2,3,4,17,22],[10,16,129]),([0,1,2,3,4,164],[0,1,4,5,10,11,16,124,142,243,260,261]),([0,1,2,3,4,17,164],[4,5,10,11,16,17,18]),([0,1,2,3,4,17,26],[16,124,129]),([0,1,2,3,4,39],[0,1,4,5,10,11,54,81,262,263,264]),([0,1,2,3,4,17,39],[4,5,11,17,18,85,124,129]),([0,1,2,3,4,6,164],[0,1,4,5,10,11,16,81,260]),([0,1,2,3,4,17,45],[5,81,85,124,128,265]),([0,1,2,3,4,6,39],[0,1,4,5,11,81,124,129,262]),([0,1,2,3,4,165],[0,1,10,11,56,124,266,267,268]),([0,1,2,3,4,17],[10,11,18,124]),([0,1,2,3,4,75],[0,1,10,11,81,144,269,270,271]),([0,1,2,3,4,24,45],[10,86,233]),([0,1,2,3,4,131],[0,1,6,7,10,11,28,81,108,244,272,273]),([0,1,2,3,4,45,131],[6,7,10,11,28,29,30]),([0,1,2,3,4,26,45],[28,81,255]),([0,1,2,3,4,60],[0,1,6,7,10,11,66,81,86,274,275,276]),([0,1,2,3,4,45,60],[6,7,11,29,30,81,86]),([0,1,2,3,4,6,131],[0,1,6,7,10,11,28,124,272]),([0,1,2,3,4,6,60],[0,1,6,7,11,81,86,124,274]),([0,1,2,3,4,135],[0,1,10,11,68,81,277,278,279]),([0,1,2,3,4,72],[0,1,10,11,81,129,264]),([0,1,2,3,4,45],[10,11,30,81]),([1,3,4,10,12,220],[0,5,10,12,13,26,98,280,281]),([1,2,4,10,85,220],[0,4,5,12,39,81,98,103,283])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_2 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_2 = true := by decide +kernel
def h26Block6_3 : List NodeSpec := nodesWithIdentity [([1,2,3,4,10,145,220],[5,12,98,103,281,284,285]),([1,2,3,4,10,41,220],[11,12,13,98,103,206]),([1,2,3,4,171,220],[0,5,12,81,98,287,288,289]),([1,2,3,4,10,17,220],[4,5,11,16,52,85,281]),([1,2,3,4,10,178],[0,5,10,12,52,290]),([1,4,10,87,220],[0,5,10,12,22,46,81,96,103,281,291]),([1,3,4,10,111,220],[0,5,10,12,33,49,281,286,294]),([1,2,4,10,14,220],[0,5,9,12,81,88,103,286,296]),([1,2,3,4,18,220],[7,12,33,34,81,286,292,298]),([1,2,3,4,10,18,220],[7,12,33,72,103,286,292]),([1,2,3,4,32,220],[0,5,12,75,81,286,299,300]),([1,2,3,4,10,224],[5,7,10,88,91,286,293,301]),([1,2,3,4,10,220,224],[5,7,88,112,281,286,293]),([1,2,3,4,10,225],[0,5,10,12,115,286,302,303]),([1,3,4,10,12,286],[0,7,10,12,13,26,133,304,305]),([1,2,3,4,10,85,286],[7,12,133,137,201,305,307]),([1,2,3,10,145,286],[0,6,7,12,43,124,133,137,309]),([1,2,3,4,10,41,286],[11,12,13,133,137,206]),([1,2,3,4,171,286],[0,7,12,124,133,289,310,311]),([1,2,3,4,10,45,286],[6,7,11,28,64,128,305]),([1,2,3,4,10,175],[0,7,10,12,64,312]),([1,3,4,10,87,286],[0,7,10,12,22,46,305,308,313]),([1,3,10,111,286],[0,7,10,12,33,49,124,132,137,305,315]),([1,2,3,10,14,286],[0,7,9,12,88,124,137,308,317]),([1,2,3,4,44,286],[5,12,22,23,124,308,316,319]),([1,2,3,4,10,44,286],[5,12,22,60,137,308,316]),([1,2,3,4,54,286],[0,7,12,63,124,308,320,321]),([1,2,3,4,10,224,286],[5,7,88,145,293,301,305]),([1,2,3,4,10,239],[0,7,10,12,146,301]),([0,3,4,10,12,85],[1,2,4,10,12,13,173,280,307]),([0,3,4,10,12,145],[1,2,6,10,12,13,192,284,304]),([0,1,3,4,10,12,14],[2,8,9,12,13,26,280]),([0,1,3,4,12,44],[1,5,12,21,22,60,324,325]),([0,1,3,4,10,12,44],[2,5,12,21,22,23,325]),([0,1,3,4,12,54],[1,10,12,13,61,325,326,327]),([0,1,3,4,10,55],[0,4,13,22,24,157,280,328]),([0,1,3,4,10,12,55],[4,13,22,24,25,26,280]),([0,1,3,4,10,59],[0,10,12,13,158,280,329,330]),([0,1,3,4,12,18],[1,7,12,32,33,72,331,332]),([0,1,3,4,10,12,18],[2,7,12,32,33,34,332]),([0,1,3,4,12,32],[1,10,12,13,73,332,333,334]),([0,1,3,4,10,33],[0,6,13,33,35,167,304,335]),([0,1,3,4,10,12,33],[6,13,26,33,35,36,304]),([0,1,3,4,10,38],[0,10,12,13,168,304,336,337]),([0,1,2,3,4,10,17],[4,10,18]),([1,2,3,4,10,17,85],[0,4,5,11,16,52,307]),([0,1,2,3,4,10,328],[4,10,18]),([0,2,3,4,10,85,145],[4,6,103,137,201,285,339]),([0,1,2,3,4,41,85],[2,12,81]),([0,2,3,4,10,41,85],[1,11,12,13,103,173]),([0,1,2,3,4,85,171],[2,12,81]),([0,1,4,10,85,87],[4,10,12,22,45,81,103,171,307]),([0,1,3,4,10,85,111],[12,33,39,48,49,137,201]),([0,1,2,3,4,10,55],[0,4,24,157]),([0,1,3,4,10,55,85],[4,10,13,22,24,39,328]),([0,1,2,3,4,10,127],[0,4,157]),([0,1,2,4,10,14,85],[2,4,8,88,137,180,201]),([0,1,2,4,44,85],[1,5,12,21,22,103,341,342]),([0,1,2,3,4,44,85],[1,12,21,103]),([0,1,2,4,10,44,85],[2,5,12,21,22,81,341]),([0,1,2,3,4,54,85],[1,12,61,103]),([0,1,2,3,4,18,85],[1,4,32,34,72,81,137]),([0,1,2,3,4,32,85],[1,4,12,73,75,81,137,334]),([0,1,2,3,4,10,88],[0,10,12,87,89,186,201]),([0,1,2,3,4,10,89],[0,4,10,12,187,189,201,344]),([0,1,2,3,4,10,22],[4,16,137]),([0,1,2,3,4,22,85],[12,201,219]),([0,1,2,3,4,85,91],[345]),([0,1,2,3,4,10,35],[346]),([0,1,2,3,4,10,45],[6,10,30])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_3 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_3 = true := by decide +kernel
def h26Block6_4 : List NodeSpec := nodesWithIdentity [([1,2,3,4,10,45,145],[0,6,7,11,28,64,284]),([0,1,2,3,4,10,324],[6,10,30]),([0,1,2,3,4,41,145],[2,12,124]),([0,2,3,4,10,41,145],[1,11,12,13,137,192]),([0,1,2,3,4,145,171],[2,12,124]),([0,1,3,4,10,87,145],[12,22,43,45,46,103,285]),([0,1,3,10,111,145],[6,10,12,33,48,124,137,190,284]),([0,1,2,3,4,10,33],[0,6,35,167]),([0,1,3,4,10,33,145],[6,10,13,33,35,43,335]),([0,1,2,3,4,10,160],[0,6,167]),([0,1,2,3,10,14,145],[2,6,8,88,103,197,285]),([0,1,2,3,4,44,145],[1,6,21,23,60,103,124]),([0,1,2,3,4,54,145],[1,6,12,61,63,103,124,327]),([0,1,2,3,4,10,123],[0,6,10,12,186,202,350]),([0,1,2,3,18,145],[1,7,12,32,33,137,351,352]),([0,1,2,3,4,18,145],[1,12,32,137]),([0,1,2,3,10,18,145],[2,7,12,32,33,124,351]),([0,1,2,3,4,32,145],[1,12,73,137]),([0,1,2,3,4,10,24],[6,103,233]),([0,1,2,3,4,24,145],[12,32,285]),([0,1,2,3,4,145,148],[353]),([0,1,2,3,4,10,36],[354]),([0,1,3,4,10,41,87],[11,12,13,26,45,103]),([0,1,3,4,10,41,111],[11,12,13,26,48,137]),([0,1,2,3,4,41,44],[1,2,11,81,103,324]),([0,1,2,3,4,41,53],[1,2,11,81]),([0,1,2,3,4,10,254],[0,1,10,11,12,13,81,236]),([0,1,2,3,4,18,41],[1,2,11,124,137,355]),([0,1,2,3,4,31,41],[1,2,11,124]),([0,1,2,3,4,10,247],[0,1,10,11,12,13,124,239]),([0,1,3,4,87,171],[4,10,12,81,288,356,357,358]),([0,1,3,4,111,171],[6,10,12,124,311,356,359,360]),([0,1,2,3,4,14,171],[2,12,81,88,124,288,289,356]),([0,1,2,3,4,204],[0,1,12,21,124,361]),([0,1,2,3,4,215],[0,1,12,32,81,362]),([0,1,3,4,10,55,87],[4,13,22,24,46,178,328]),([0,1,3,4,10,172],[0,10,11,22,328,363]),([0,1,4,10,14,87],[10,12,22,51,81,88,103,208,313]),([0,1,3,4,18,87],[7,12,33,72,81,292,313,365]),([0,1,3,4,10,18,87],[7,12,33,34,103,292,313]),([0,1,3,4,32,87],[10,12,22,81,300,313,334,366]),([0,1,3,4,10,90],[0,22,33,88,212,213,313,367]),([0,1,3,4,10,87,90],[22,33,46,88,212,214,313]),([0,1,3,4,10,94],[0,10,12,22,215,216,313,369]),([0,1,3,4,10,33,111],[6,13,33,35,49,195,335]),([0,1,3,4,10,186],[0,10,11,33,335,370]),([0,1,3,10,14,111],[10,12,33,51,88,124,137,224,294]),([0,1,3,4,44,111],[5,12,22,60,124,294,316,372]),([0,1,3,4,10,44,111],[5,12,22,23,137,294,316]),([0,1,3,4,54,111],[10,12,33,124,294,321,327,373]),([0,1,3,4,10,90,111],[22,33,49,88,130,212,367]),([0,1,3,4,10,122],[0,10,12,33,226,227,294,374]),([0,1,2,3,4,10,224],[10,88,91]),([1,2,3,4,10,14,224],[0,5,7,51,88,293,301]),([0,1,2,3,4,10,323],[9,10,88]),([0,1,2,3,4,10,174],[0,8,10,12,88,246,376,377]),([0,1,2,3,4,10,90],[0,88,212,213]),([0,1,3,4,10,14,90],[9,10,22,33,88,212,367]),([0,1,2,3,4,10,130],[0,51,88,247]),([0,1,2,4,14,44],[5,12,22,103,124,316,378,379]),([0,1,2,3,4,14,44],[12,103,124]),([0,1,2,4,10,14,44],[5,12,22,81,137,316,378]),([0,1,2,3,4,14,54],[12,103,124]),([0,1,2,3,14,18],[7,12,33,81,137,292,381,382]),([0,1,2,3,4,14,18],[12,81,137,292]),([0,1,2,3,10,14,18],[7,12,33,103,124,292,381]),([0,1,2,3,4,14,32],[12,81,137,300]),([0,1,2,3,4,28],[1,292,384]),([0,1,2,3,4,10,28],[2,88]),([0,1,2,3,4,14,28],[8,12,292])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_4 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_4 = true := by decide +kernel
def h26Block6_5 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,14,29],[387]),([0,1,2,3,4,10,34],[388]),([0,1,2,3,4,22,44],[1,219,316]),([0,1,2,3,4,189],[0,1,5,12,21,22,124,220,361,389,390]),([0,1,2,3,4,44,189],[1,5,12,21,22,23]),([0,1,2,3,4,28,44],[21,124,384]),([0,1,2,3,4,51],[0,1,5,10,12,22,59,81,391,392,393]),([0,1,2,3,4,44,51],[5,12,22,23,60,103,124,316]),([0,1,2,3,4,10,189],[0,1,2,5,11,21,22,81,389]),([0,1,2,3,4,18,44],[5,81,103,124,137,394]),([0,1,2,3,4,10,51],[0,5,10,12,22,81,124,316,391]),([0,1,2,3,4,192],[0,1,10,11,12,61,124,395,396,397]),([0,1,2,3,4,44],[1,12,23,124]),([0,1,2,3,4,77],[0,1,10,12,81,321,398,399,400]),([0,1,2,3,4,18,24],[1,32,292]),([0,1,2,3,4,176],[0,1,7,12,32,33,81,232,362,401,402]),([0,1,2,3,4,18,176],[1,7,12,32,33,34]),([0,1,2,3,4,18,28],[32,81,292]),([0,1,2,3,4,61],[0,1,7,10,12,33,71,81,292,403,404,405]),([0,1,2,3,4,18,61],[7,12,33,34,72,81,292]),([0,1,2,3,4,10,176],[0,1,2,7,11,32,33,124,401]),([0,1,2,3,4,10,61],[0,7,10,12,33,81,124,292,403]),([0,1,2,3,4,179],[0,1,10,11,12,73,81,406,407,408]),([0,1,2,3,4,70],[0,1,10,12,81,300,409,410,411]),([0,1,2,3,4,18],[1,12,34,81]),([1,2,3,4,12,220,286],[5,7,145,178,195,412,414]),([1,2,4,85,220,286],[0,4,5,7,39,81,412,414,416]),([1,2,3,145,220,286],[0,5,6,7,43,124,145,412,418]),([1,2,3,4,17,220,286],[4,5,11,85,129,141,145]),([1,2,3,4,178,286],[0,5,7,124,141,290]),([1,2,3,4,45,220,286],[6,7,11,86,107,128,414]),([1,2,3,4,175,220],[0,5,7,81,107,312]),([1,2,4,87,220,286],[0,5,7,22,46,81,414,415,419]),([1,2,3,111,220,286],[0,5,7,33,49,124,145,415,421]),([1,2,3,4,44,220,286],[5,12,22,103,145,316,319]),([1,2,3,4,134,286],[0,5,7,104,124,319]),([1,2,3,4,18,220,286],[7,12,33,137,292,298,414]),([1,2,3,4,132,220],[0,5,7,81,138,298]),([1,2,14,220,286],[0,5,7,9,81,88,124,145,413,414,422]),([0,1,2,3,4,41,220],[13,26,81]),([1,2,3,4,12,41,220],[0,11,12,13,98,178]),([0,1,2,3,4,220,320],[13,26,81]),([0,2,4,12,85,220],[1,4,5,13,76,81,173,178,283]),([0,2,3,4,12,145,220],[6,13,145,192,195,281,284]),([0,1,2,3,4,12,17],[5,10,17]),([0,2,3,4,12,17,220],[1,4,5,11,16,151,281]),([0,1,2,3,4,12,178],[5,10,17]),([0,1,4,12,87,220],[5,10,13,22,81,95,147,178,281]),([0,1,3,4,12,111,220],[13,33,76,82,145,149,195]),([0,1,2,3,4,12,44],[1,5,21,60]),([0,1,3,4,12,44,220],[5,10,12,21,22,76,324]),([0,1,2,3,4,12,134],[1,5,60]),([0,1,2,4,12,14,220],[5,9,26,88,105,145,195]),([0,1,2,4,55,220],[0,4,13,22,24,178,424,425]),([0,1,2,3,4,55,220],[0,13,24,178]),([0,1,2,4,12,55,220],[4,13,22,24,26,81,424]),([0,1,2,3,4,59,220],[0,13,158,178]),([0,1,2,3,4,33,220],[0,5,35,36,81,167,195]),([0,1,2,3,4,38,220],[0,5,13,81,168,170,195,337]),([0,1,2,3,4,12,224],[1,10,13,90,91,112,145]),([0,1,2,3,4,12,225],[1,5,10,13,113,115,145,427]),([0,1,2,3,4,12,22],[5,195,219]),([0,1,2,3,4,22,220],[13,145]),([0,1,2,3,4,220,221],[429]),([0,1,2,3,4,12,23],[430]),([0,2,4,85,145,220],[1,4,5,6,76,81,285,339,416]),([0,1,2,4,85,111,220],[4,5,39,49,76,82,283]),([0,1,2,4,55,85,220],[4,13,22,24,25,39,425]),([0,1,2,4,127,220],[0,4,12,81,425,432]),([0,1,2,4,44,85,220],[5,12,21,22,23,76,342])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_5 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_5 = true := by decide +kernel
def h26Block6_6 : List NodeSpec := nodesWithIdentity [([0,1,2,4,85,134],[1,5,13,81,433,434]),([0,1,2,4,88,220],[0,4,6,87,88,186,416,435]),([0,1,2,4,85,88,220],[4,6,39,87,88,89,416]),([0,1,2,4,89,220],[0,4,5,81,187,344,416,436]),([0,1,2,4,85,224],[1,5,7,88,90,112,416,437]),([0,1,2,4,85,220,224],[5,7,76,88,90,91,416]),([0,1,2,4,85,225],[1,4,5,81,113,416,427,438]),([0,1,2,3,4,45,220],[6,30,81]),([1,2,3,4,45,145,220],[0,6,7,11,86,107,285]),([0,1,2,3,4,220,324],[6,30,81]),([0,1,2,3,4,17,145],[5,17,124]),([0,2,3,4,17,145,220],[1,4,5,11,129,145,199]),([0,1,2,3,4,145,178],[5,17,124]),([0,1,2,4,87,145,220],[5,22,43,46,95,281,284]),([0,1,2,3,111,145,220],[6,33,76,82,190,281,284]),([0,1,2,3,4,160,220],[0,5,6,81,167,196,441]),([0,1,2,3,4,134,145],[1,5,6,60,104,124,434]),([0,1,2,14,145,220],[5,6,81,88,105,124,145,197,285]),([0,1,2,3,4,88,220],[0,6,87,186]),([0,1,2,4,88,145,220],[4,6,43,81,87,88,435]),([0,1,2,3,4,123,220],[0,6,186]),([0,1,2,3,145,224],[1,5,7,88,90,145,442,443]),([0,1,2,3,4,145,224],[1,5,90,145]),([0,1,2,3,145,220,224],[5,7,76,88,90,124,442]),([0,1,2,3,4,145,225],[1,5,113,145]),([0,1,2,3,4,26,145],[5,129,284]),([0,1,2,3,4,26,220],[6,255,281]),([0,1,2,3,4,220,222],[445]),([0,1,2,3,4,145,152],[446]),([0,1,2,4,17,87,220],[4,5,11,16,18,210,281]),([0,1,2,3,4,164,220],[0,1,4,10,11,12,16,260,281]),([0,1,2,3,4,17,44],[1,10,11,17,60,447]),([0,1,2,4,14,17,220],[4,5,11,18,129,145,251]),([0,1,2,3,4,39,220],[0,1,4,5,11,81,124,129,262]),([0,1,2,3,4,17,224],[1,11,17,124,145,448]),([0,1,2,4,87,178],[5,10,13,81,449,450]),([0,1,2,3,4,110,178],[5,10,17,290,449]),([0,1,2,3,4,111,178],[5,10,17,33,124,290,449]),([0,1,2,3,4,120,178],[5,10,290,449]),([0,1,2,3,4,124,178],[5,124,290,449]),([0,1,2,3,4,203],[0,1,5,12,21,124,390]),([0,1,2,4,14,178],[5,6,81,124,251,449]),([0,1,2,3,4,281],[0,1,5,10]),([0,1,2,4,55,87,220],[4,13,22,24,46,157,424]),([0,1,2,4,172,220],[0,11,22,81,424,451]),([0,1,4,87,111,220],[5,10,22,33,81,97,204,281,419]),([0,1,2,4,90,220],[0,22,33,88,212,214,419,453]),([0,1,2,4,87,90,220],[22,33,46,88,212,213,419]),([0,1,2,4,94,220],[0,5,22,81,215,217,419,454]),([0,1,2,4,87,224],[5,7,10,88,112,293,419,455]),([0,1,2,4,87,220,224],[5,7,88,91,281,293,419]),([0,1,2,4,87,225],[5,10,22,81,302,419,427,456]),([0,1,2,3,4,18,220],[33,34,81]),([1,2,3,4,18,111,220],[0,7,12,33,97,292,298]),([0,1,2,3,4,220,336],[33,34,81]),([0,1,2,3,4,186,220],[0,5,33,36,81,370,458]),([0,1,2,3,4,44,111],[5,60,124]),([0,1,3,4,44,111,220],[5,10,12,22,145,316,372]),([0,1,2,3,4,111,134],[5,60,124]),([0,1,2,14,111,220],[5,33,81,88,97,124,145,224,296]),([0,1,2,3,4,90,220],[0,33,212,214]),([0,1,2,4,90,111,220],[22,33,49,81,88,212,453]),([0,1,2,3,4,122,220],[0,33,97,226]),([0,1,2,3,111,224],[5,7,10,88,145,293,460,461]),([0,1,2,3,4,111,224],[5,10,145,293]),([0,1,2,3,111,220,224],[5,7,88,124,281,293,460]),([0,1,2,3,4,111,225],[5,10,145,302]),([0,1,2,3,4,28,111],[5,82,384]),([0,1,2,3,4,28,220],[33,76,292]),([0,1,2,3,4,220,223],[463])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_6 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_6 = true := by decide +kernel
def h26Block6_7 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,111,119],[464]),([0,1,2,3,4,189,220],[0,1,10,11,12,21,22,76,389]),([0,1,2,4,14,44,220],[5,12,22,23,145,316,379]),([0,1,2,3,4,51,220],[0,5,10,12,22,81,124,316,391]),([0,1,2,3,4,44,224],[10,12,60,124,145,465]),([0,1,2,3,4,134,144],[1,5,60,104,434]),([0,1,2,3,4,134,153],[1,5,104,434]),([0,1,2,3,4,134,170],[5,104,124,434]),([0,1,2,3,4,198],[0,1,5,10,11,16,124,261]),([0,1,2,4,14,134],[5,33,81,124,379,434]),([0,1,2,3,4,240],[0,1,5,10,466]),([0,1,2,4,14,88,220],[4,6,9,87,88,201,435]),([0,1,2,4,174,220],[0,11,81,88,105,246,376,467]),([0,1,2,4,14,90,220],[9,22,33,88,130,212,453]),([0,1,2,4,130,220],[0,12,81,88,247,248,296,468]),([0,1,2,3,4,26,224],[1,293]),([0,1,2,3,4,177],[0,1,5,7,10,88]),([0,1,2,3,4,177,224],[1,5,7,88,90,91]),([0,1,2,3,4,28,224],[10,90]),([0,1,2,3,4,133],[0,1,5,7,10,88]),([0,1,2,3,4,133,224],[5,7,10,88,91,293]),([0,1,2,3,4,177,220],[0,1,7,11,76,88,124]),([0,1,2,3,4,133,220],[0,7,10,12,88,124,281]),([0,1,2,3,4,180],[0,1,5,10,11,81,129,263]),([0,1,2,3,4,136],[0,1,5,10,12,81,316,392]),([0,1,2,3,4,224],[1,5,10,91]),([0,1,2,3,4,41,286],[13,26,124]),([1,2,3,4,12,41,286],[0,11,12,13,133,195]),([0,1,2,3,4,286,320],[13,26,124]),([0,2,3,4,12,85,286],[4,13,173,178,305,307,414]),([0,2,3,12,145,286],[1,6,7,13,116,124,192,195,309]),([0,1,2,3,4,12,45],[7,10,29]),([0,2,3,4,12,45,286],[1,6,7,11,28,161,305]),([0,1,2,3,4,12,175],[7,10,29]),([0,1,3,4,12,87,286],[13,22,116,125,147,178,414]),([0,1,3,12,111,286],[7,10,13,33,124,131,149,195,305]),([0,1,2,3,4,12,18],[1,7,32,72]),([0,1,3,4,12,18,286],[7,10,12,32,33,116,331]),([0,1,2,3,4,12,132],[1,7,72]),([0,1,2,3,12,14,286],[7,9,26,88,139,178,414]),([0,1,2,3,4,55,286],[0,7,24,25,124,157,178]),([0,1,2,3,4,59,286],[0,7,13,124,158,160,178,330]),([0,1,2,3,4,12,239],[1,7,10,13,112,146,474]),([0,1,2,3,33,286],[0,6,13,33,35,195,475,476]),([0,1,2,3,4,33,286],[0,13,35,195]),([0,1,2,3,12,33,286],[6,13,26,33,35,124,475]),([0,1,2,3,4,38,286],[0,13,168,195]),([0,1,2,3,4,12,24],[7,32,178]),([0,1,2,3,4,24,286],[13,414]),([0,1,2,3,4,286,289],[478]),([0,1,2,3,4,12,25],[479]),([0,1,2,3,4,17,286],[4,18,124]),([1,2,3,4,17,85,286],[0,4,5,11,129,141,201]),([0,1,2,3,4,286,328],[4,18,124]),([0,2,3,85,145,286],[1,4,6,7,116,124,201,339,418]),([0,1,2,3,4,45,85],[7,29,81]),([0,2,3,4,45,85,286],[1,6,7,11,86,182,414]),([0,1,2,3,4,85,175],[7,29,81]),([0,1,2,4,85,87,286],[4,22,116,125,171,305,307]),([0,1,2,3,85,111,286],[7,33,39,49,131,305,307]),([0,1,2,3,4,127,286],[0,4,7,124,157,179,432]),([0,1,2,3,4,85,132],[1,4,7,72,81,138,482]),([0,1,2,14,85,286],[4,7,81,88,124,139,180,201,414]),([0,1,2,3,4,85,224],[1,7,90,112]),([0,1,2,4,85,224,286],[5,7,81,88,90,116,437]),([0,1,2,3,4,85,239],[1,7,112]),([0,1,2,3,88,286],[0,4,6,87,88,201,483,484]),([0,1,2,3,4,88,286],[0,4,87,201]),([0,1,2,3,85,88,286],[4,6,39,87,88,124,483]),([0,1,2,3,4,89,286],[0,4,187,201])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_7 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_7 = true := by decide +kernel
def h26Block6_8 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,26,85],[7,255,307]),([0,1,2,3,4,26,286],[4,129,305]),([0,1,2,3,4,286,292],[485]),([0,1,2,3,4,85,92],[486]),([0,1,2,3,87,145,286],[6,7,43,46,116,125,309]),([0,1,2,3,33,145,286],[6,13,33,35,36,43,476]),([0,1,2,3,160,286],[0,6,12,124,441,476]),([0,1,2,3,18,145,286],[7,12,32,33,34,116,352]),([0,1,2,3,132,145],[1,7,13,124,352,482]),([0,1,2,3,88,145,286],[4,6,43,87,88,89,484]),([0,1,2,3,123,286],[0,5,6,124,350,484]),([0,1,2,3,145,224,286],[5,7,88,90,91,116,443]),([0,1,2,3,145,239],[1,4,7,124,443,474]),([0,1,2,3,45,111,286],[6,7,11,28,30,230,305]),([0,1,2,3,4,131,286],[0,1,6,10,11,12,28,272,305]),([0,1,2,3,4,18,45],[1,10,11,29,72,487]),([0,1,2,3,14,45,286],[6,7,11,30,86,254,414]),([0,1,2,3,4,60,286],[0,1,5,6,11,81,86,274,414]),([0,1,2,3,4,45,224],[1,11,29,81,112,488]),([0,1,2,3,4,86,175],[7,10,29,312,489]),([0,1,2,3,4,87,175],[7,10,22,29,81,312,489]),([0,1,2,3,4,108,175],[7,10,312,489]),([0,1,2,3,4,109,175],[7,81,312,489]),([0,1,2,3,111,175],[7,10,13,124,489,490]),([0,1,2,3,4,213],[0,1,7,12,32,81,402]),([0,1,2,3,14,175],[4,7,81,124,254,489]),([0,1,2,3,4,280],[0,1,5,7,10]),([0,1,2,3,4,44,286],[22,23,124]),([1,2,3,4,44,87,286],[0,5,12,22,130,316,319]),([0,1,2,3,4,286,321],[22,23,124]),([0,1,2,3,4,172,286],[0,7,22,25,124,363,451]),([0,1,3,87,111,286],[7,10,22,33,124,130,204,305,421]),([0,1,2,3,4,18,87],[7,72,81]),([0,1,3,4,18,87,286],[7,10,12,33,292,365,414]),([0,1,2,3,4,87,132],[7,72,81]),([0,1,2,14,87,286],[7,22,81,88,124,130,208,317,414]),([0,1,2,3,4,87,224],[7,10,112,293]),([0,1,2,4,87,224,286],[5,7,81,88,293,305,455]),([0,1,2,3,4,87,239],[7,10,112]),([0,1,2,3,90,286],[0,22,33,88,130,212,493,494]),([0,1,2,3,4,90,286],[0,22,130,212]),([0,1,2,3,87,90,286],[22,33,46,88,124,212,493]),([0,1,2,3,4,94,286],[0,22,130,215]),([0,1,2,3,4,28,87],[7,125,292]),([0,1,2,3,4,28,286],[22,116,384]),([0,1,2,3,4,286,291],[495]),([0,1,2,3,4,87,102],[496]),([0,1,2,3,33,111,286],[6,13,33,35,49,167,475]),([0,1,2,3,186,286],[0,11,33,124,458,475]),([0,1,2,3,90,111,286],[22,33,49,88,212,213,494]),([0,1,2,3,122,286],[0,5,33,124,226,228,421,497]),([0,1,2,3,111,224,286],[5,7,88,91,293,305,461]),([0,1,2,3,111,239],[7,10,22,124,461,474]),([0,1,2,3,4,176,286],[0,1,10,11,12,32,33,116,401]),([0,1,2,3,14,18,286],[7,12,33,34,292,382,414]),([0,1,2,3,4,61,286],[0,5,10,12,33,81,292,403,414]),([0,1,2,3,4,18,224],[10,12,72,81,112,498]),([0,1,2,3,4,84,132],[1,7,72,138,482]),([0,1,2,3,4,121,132],[1,7,138,482]),([0,1,2,3,4,132,143],[7,81,138,482]),([0,1,2,3,4,208],[0,1,7,10,11,28,81,273]),([0,1,2,3,14,132],[7,22,81,124,382,482]),([0,1,2,3,4,258],[0,1,5,7,10]),([0,1,2,3,14,88,286],[4,6,9,87,88,186,483]),([0,1,2,3,174,286],[0,11,88,124,139,246,377,499]),([0,1,2,3,14,90,286],[9,22,33,88,212,214,493]),([0,1,2,3,130,286],[0,12,88,124,247,249,317,500]),([0,1,2,3,4,177,286],[0,1,5,11,81,88,116]),([0,1,2,3,4,133,286],[0,5,10,12,81,88,305]),([0,1,2,3,4,11,239],[1,7,112,146,474])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_8 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_8 = true := by decide +kernel
def h26Block6_9 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,82,239],[1,7,146,474]),([0,1,2,3,4,83,239],[7,10,146,474]),([0,1,2,3,4,193],[0,1,7,10,11,81,86,275]),([0,1,2,3,4,169],[0,1,7,10,12,81,292,404]),([0,2,3,4,12,41,85],[11,12,13,173,178,206]),([0,2,3,4,12,41,145],[11,12,13,192,195,206]),([0,1,3,4,12,41,87],[2,11,12,13,147,178]),([0,1,3,4,12,41,111],[2,11,12,13,149,195]),([0,1,2,3,4,41,55],[0,11,26,81,178,328]),([0,1,2,3,4,41,58],[0,11,26,81]),([0,1,2,3,4,12,254],[0,1,10,11,12,13,81,237]),([0,1,2,3,4,33,41],[0,11,26,124,195,502]),([0,1,2,3,4,37,41],[0,11,26,124]),([0,1,2,3,4,12,247],[0,1,10,11,12,13,124,240]),([0,2,3,4,85,320],[1,5,13,81,504,506,507,508]),([0,2,3,4,145,320],[1,7,13,124,504,509,510,511]),([0,1,3,4,87,320],[5,10,13,81,505,508,512,513]),([0,1,3,4,111,320],[7,10,13,124,505,511,514,515]),([0,1,2,3,4,14,320],[13,26,81,88,124,504,505,508]),([0,1,2,3,4,348],[0,13,24,124,516]),([0,1,2,3,4,355],[0,13,35,81,517]),([0,2,3,4,12,17,85],[4,5,11,16,85,151,307]),([0,2,3,4,12,328],[1,4,10,12,151,519]),([0,4,12,85,87],[1,4,10,13,22,81,125,172,178,307,520]),([0,3,4,12,85,111],[1,4,10,13,33,82,307,518,525]),([0,2,4,12,14,85],[1,4,8,13,81,88,178,518,527]),([0,2,3,4,33,85],[6,13,33,36,81,518,521,529]),([0,2,3,4,12,33,85],[6,13,33,167,178,518,521]),([0,2,3,4,38,85],[1,4,13,81,170,518,530,531]),([0,2,3,4,12,88],[4,6,10,88,89,518,523,532]),([0,2,3,4,12,85,88],[4,6,88,186,307,518,523]),([0,2,3,4,12,89],[1,4,10,13,189,518,533,534]),([0,2,3,4,12,45,145],[6,7,11,28,128,161,284]),([0,2,3,4,12,324],[1,6,10,12,161,536]),([0,3,4,12,87,145],[1,6,10,13,22,125,284,535,537]),([0,3,12,111,145],[1,6,10,13,33,82,124,191,195,284,539]),([0,2,3,12,14,145],[1,6,8,13,88,124,195,535,541]),([0,2,3,4,55,145],[4,13,22,25,124,535,540,543]),([0,2,3,4,12,55,145],[4,13,22,157,195,535,540]),([0,2,3,4,59,145],[1,6,13,124,160,535,544,545]),([0,2,3,4,12,88,145],[4,6,88,201,284,523,532]),([0,2,3,4,12,123],[1,6,10,13,202,532]),([0,1,3,4,12,44,87],[5,12,21,22,103,125,324]),([0,1,3,4,12,321],[1,10,11,22,324,546]),([0,1,4,12,14,87],[10,13,22,51,81,88,178,537,547]),([0,1,3,4,33,87],[6,13,33,81,167,521,537,549]),([0,1,3,4,12,33,87],[6,13,33,36,178,521,537]),([0,1,3,4,38,87],[10,13,22,81,337,531,537,550]),([0,1,3,4,12,90],[1,22,33,88,213,524,537,551]),([0,1,3,4,12,87,90],[22,33,88,125,214,524,537]),([0,1,3,4,12,94],[1,10,13,22,216,537,552,553]),([0,1,3,4,12,18,111],[7,12,32,33,82,137,331]),([0,1,3,4,12,336],[1,10,11,33,331,554]),([0,1,3,12,14,111],[10,13,33,51,88,124,195,525,555]),([0,1,3,4,55,111],[4,13,22,124,157,525,540,557]),([0,1,3,4,12,55,111],[4,13,22,25,195,525,540]),([0,1,3,4,59,111],[10,13,33,124,330,525,545,558]),([0,1,3,4,12,90,111],[22,33,82,88,130,524,551]),([0,1,3,4,12,122],[1,10,13,33,227,525,559,560]),([0,1,2,3,4,12,323],[1,9,10,13,88,561,562,563]),([0,1,2,3,4,12,88],[10,88,89]),([0,2,3,4,12,14,88],[1,4,6,51,88,523,532]),([0,1,2,3,4,12,174],[8,10,88]),([0,1,2,3,4,12,90],[1,88,213,524]),([0,1,3,4,12,14,90],[8,10,22,33,88,524,551]),([0,1,2,3,4,12,130],[1,51,88,565]),([0,1,2,4,14,55],[4,13,22,124,178,540,566,567]),([0,1,2,3,4,14,55],[13,124,178]),([0,1,2,4,12,14,55],[4,13,22,81,195,540,566]),([0,1,2,3,4,14,59],[13,124,178])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_9 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_9 = true := by decide +kernel
def h26Block6_10 : List NodeSpec := nodesWithIdentity [([0,1,2,3,14,33],[6,13,33,81,195,521,569,570]),([0,1,2,3,4,14,33],[13,81,195,521]),([0,1,2,3,12,14,33],[6,13,33,124,178,521,569]),([0,1,2,3,4,14,38],[13,81,195,531]),([0,1,2,3,4,19],[0,571,572,573,574]),([0,1,2,3,4,12,19],[26,88,571]),([0,1,2,3,4,14,19],[9,13,573]),([0,1,2,3,4,14,20],[577]),([0,1,2,3,4,12,21],[578]),([0,1,2,3,4,22,55],[0,540]),([0,1,2,3,4,340],[0,4,13,22,24,124,218,516,580,581]),([0,1,2,3,4,55,340],[0,4,13,22,24]),([0,1,2,3,4,19,55],[24,124,574]),([0,1,2,3,4,56],[0,1,4,10,13,22,81,156,582,583,584]),([0,1,2,3,4,55,56],[4,13,22,25,124,157,178,540]),([0,1,2,3,4,12,340],[0,4,11,22,24,26,81,580]),([0,1,2,3,4,33,55],[4,81,124,178,195,585]),([0,1,2,3,4,12,56],[1,4,10,13,22,81,124,540,582]),([0,1,2,3,4,342],[0,1,10,11,12,13,124,158,586,587,588]),([0,1,2,3,4,55],[0,13,24,25,124]),([0,1,2,3,4,78],[0,1,10,13,81,545,589,590,591]),([0,1,2,3,4,24,33],[0,521]),([0,1,2,3,4,326],[0,6,13,33,35,81,231,517,593,594]),([0,1,2,3,4,33,326],[0,6,13,33,35]),([0,1,2,3,4,19,33],[35,81,573]),([0,1,2,3,4,62],[0,1,6,10,13,33,81,166,521,595,596,597]),([0,1,2,3,4,33,62],[6,13,33,36,81,167,521]),([0,1,2,3,4,12,326],[0,6,11,26,33,35,124,593]),([0,1,2,3,4,12,62],[1,6,10,13,33,81,124,521,595]),([0,1,2,3,4,329],[0,1,10,11,12,13,81,168,598,599,600]),([0,1,2,3,4,71],[0,1,10,13,81,531,601,602,603]),([0,1,2,3,4,33],[0,13,35,36,81]),([0,2,3,4,17,85,145],[4,5,11,85,129,199,201]),([0,1,2,4,17,85,87],[4,5,11,16,17,209,307]),([0,1,2,3,4,85,164],[0,1,5,10,11,13,16,261,307]),([0,1,2,3,4,17,55],[0,10,11,18,157,604]),([0,1,2,4,14,17,85],[4,5,11,17,129,201,250]),([0,1,2,3,4,39,85],[0,1,4,5,11,81,124,129,263]),([0,1,2,3,4,17,88],[0,11,18,124,201,605]),([0,2,3,4,145,328],[1,4,7,124,519,607]),([0,1,2,4,87,328],[4,10,12,81,606,608]),([0,1,2,3,4,110,328],[4,10,18,519,606]),([0,1,2,3,4,111,328],[4,10,18,33,124,519,606]),([0,1,2,3,4,120,328],[4,10,519,606]),([0,1,2,3,4,124,328],[4,124,519,606]),([0,1,2,3,4,347],[0,4,13,24,124,581]),([0,1,2,4,14,328],[4,7,81,124,250,606]),([0,1,2,3,4,369],[0,4,10]),([0,2,3,4,45,85,145],[6,7,11,86,128,182,285]),([0,2,3,4,85,324],[1,5,6,81,536,610]),([0,2,4,85,87,145],[1,4,6,22,81,125,285,609,611]),([0,2,3,85,111,145],[1,4,6,33,82,124,201,609,613]),([0,2,3,4,55,85,145],[4,13,22,178,201,540,543]),([0,2,3,4,127,145],[1,4,6,124,179,543]),([0,2,3,4,33,85,145],[6,13,33,195,285,521,529]),([0,2,3,4,85,160],[1,4,6,81,196,614]),([0,2,14,85,145],[1,4,6,8,81,88,124,201,285,340,615]),([0,1,2,4,44,85,87],[5,12,21,22,60,125,341]),([0,1,2,4,85,321],[1,11,22,81,616,617]),([0,1,4,85,87,111],[4,10,22,33,81,97,307,611,618]),([0,1,2,4,87,88],[4,6,10,88,186,523,620,621]),([0,1,2,4,85,87,88],[4,6,88,89,307,523,621]),([0,1,2,4,87,89],[4,10,22,81,344,533,621,622]),([0,1,2,4,85,90],[1,22,33,88,214,524,611,623]),([0,1,2,4,85,87,90],[22,33,88,125,213,524,611]),([0,1,2,4,85,94],[1,4,22,81,217,552,611,624]),([0,1,2,3,4,85,336],[1,4,33,34,81,554,625]),([0,1,2,3,4,33,85],[33,36,81]),([0,2,3,4,33,85,111],[1,6,13,33,97,521,529]),([0,1,2,3,4,85,186],[33,36,81])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_10 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_10 = true := by decide +kernel
def h26Block6_11 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,55,111],[4,124,157]),([0,1,3,4,55,85,111],[4,10,13,22,201,540,557]),([0,1,2,3,4,111,127],[4,124,157]),([0,1,2,14,85,111],[4,33,81,88,97,124,201,527,555]),([0,1,2,3,4,85,90],[1,33,214,524]),([0,1,2,4,85,90,111],[22,33,81,82,88,524,623]),([0,1,2,3,4,85,122],[1,33,97,559]),([0,1,2,3,88,111],[4,6,10,88,201,523,628,629]),([0,1,2,3,4,88,111],[4,10,201,523]),([0,1,2,3,85,88,111],[4,6,88,124,307,523,628]),([0,1,2,3,4,89,111],[4,10,201,533]),([0,1,2,3,4,19,85],[33,39,571]),([0,1,2,3,4,19,111],[4,49,572]),([0,1,2,3,4,111,118],[631]),([0,1,2,3,4,85,93],[632]),([0,1,2,3,4,85,340],[0,10,11,13,22,24,39,580]),([0,1,2,4,14,55,85],[4,13,22,25,201,540,567]),([0,1,2,3,4,56,85],[1,4,10,13,22,81,124,540,582]),([0,1,2,3,4,55,88],[10,13,124,157,201,633]),([0,1,2,3,4,127,285],[0,4,157,179,432]),([0,1,2,3,4,127,293],[0,4,179,432]),([0,1,2,3,4,127,319],[4,124,179,432]),([0,1,2,3,4,346],[0,1,4,5,10,11,16,124,260]),([0,1,2,4,14,127],[4,33,81,124,432,567]),([0,1,2,3,4,128],[0,1,4,10,634]),([0,1,2,4,14,85,224],[5,7,8,88,90,145,437]),([0,1,2,4,85,323],[1,11,81,88,561,562,635,636]),([0,1,2,4,14,85,90],[8,22,33,88,130,524,623]),([0,1,2,4,85,130],[1,13,81,88,248,565,637,638]),([0,1,2,3,4,26,88],[0,523]),([0,1,2,3,4,327],[0,4,6,10,88]),([0,1,2,3,4,88,327],[0,4,6,87,88]),([0,1,2,3,4,19,88],[10,87,572]),([0,1,2,3,4,137],[0,1,4,6,10,88,185,523,640,641,642]),([0,1,2,3,4,88,137],[4,6,10,88,89,523]),([0,1,2,3,4,85,327],[0,6,11,39,88,124]),([0,1,2,3,4,85,137],[1,6,10,13,88,124,307,523,640]),([0,1,2,3,4,330],[0,1,4,5,10,11,81,129,262]),([0,1,2,3,4,138],[0,1,4,10,13,81,533,643,644,645]),([0,1,2,3,4,88],[0,4,10,87,89]),([0,1,2,3,45,111,145],[6,7,11,28,29,229,284]),([0,1,2,3,4,131,145],[0,1,7,10,11,13,28,273,284]),([0,1,2,3,4,33,45],[0,10,11,30,167,646]),([0,1,2,3,14,45,145],[6,7,11,29,86,253,285]),([0,1,2,3,4,60,145],[0,1,4,7,11,81,86,275,285]),([0,1,2,3,4,45,88],[0,11,30,81,186,647]),([0,1,2,3,4,86,324],[6,10,30,536,648]),([0,1,2,3,4,87,324],[6,10,22,30,81,536,648]),([0,1,2,3,4,108,324],[6,10,536,648]),([0,1,2,3,4,109,324],[6,81,536,648]),([0,1,2,3,111,324],[6,10,12,124,648,649]),([0,1,2,3,4,353],[0,6,13,35,81,594]),([0,1,2,3,14,324],[5,6,81,124,253,648]),([0,1,2,3,4,368],[0,4,6,10]),([0,1,2,3,4,145,321],[1,6,22,23,124,546,617]),([0,1,2,3,4,55,145],[22,25,124]),([0,2,3,4,55,87,145],[1,4,13,22,130,540,543]),([0,1,2,3,4,145,172],[22,25,124]),([0,1,3,87,111,145],[6,10,22,33,124,130,284,613,618]),([0,1,2,3,4,33,87],[6,81,167]),([0,1,3,4,33,87,145],[6,10,13,33,285,521,549]),([0,1,2,3,4,87,160],[6,81,167]),([0,1,2,14,87,145],[6,22,81,88,124,130,285,541,547]),([0,1,2,3,4,87,88],[6,10,186,523]),([0,1,2,4,87,88,145],[4,6,81,88,284,523,620]),([0,1,2,3,4,87,123],[6,10,186]),([0,1,2,3,90,145],[1,22,33,88,130,524,652,653]),([0,1,2,3,4,90,145],[1,22,130,524]),([0,1,2,3,87,90,145],[22,33,88,124,125,524,652]),([0,1,2,3,4,94,145],[1,22,130,552])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_11 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_11 = true := by decide +kernel
def h26Block6_12 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,19,87],[6,46,572]),([0,1,2,3,4,19,145],[22,43,571]),([0,1,2,3,4,145,151],[654]),([0,1,2,3,4,87,103],[655]),([0,1,2,3,18,111,145],[7,12,32,33,72,82,351]),([0,1,2,3,145,336],[1,11,33,124,625,656]),([0,1,2,3,90,111,145],[22,33,82,88,213,524,653]),([0,1,2,3,122,145],[1,4,33,124,228,559,613,657]),([0,1,2,3,88,111,145],[4,6,88,89,284,523,629]),([0,1,2,3,111,123],[6,10,22,124,350,658]),([0,1,2,3,4,145,326],[0,10,11,13,33,35,43,593]),([0,1,2,3,14,33,145],[6,13,33,36,285,521,570]),([0,1,2,3,4,62,145],[1,4,10,13,33,81,285,521,595]),([0,1,2,3,4,33,88],[10,13,81,167,186,659]),([0,1,2,3,4,160,219],[0,6,167,196,441]),([0,1,2,3,4,160,238],[0,6,196,441]),([0,1,2,3,4,160,284],[6,81,196,441]),([0,1,2,3,4,352],[0,1,6,7,10,11,28,81,272]),([0,1,2,3,14,160],[6,22,81,124,441,570]),([0,1,2,3,4,161],[0,1,4,6,10,660]),([0,1,2,3,14,145,224],[5,7,8,88,90,112,442]),([0,1,2,3,145,323],[1,11,88,124,561,563,661,662]),([0,1,2,3,14,90,145],[8,22,33,88,214,524,652]),([0,1,2,3,130,145],[1,13,88,124,249,541,565,663]),([0,1,2,3,4,145,327],[0,4,11,43,81,88]),([0,1,2,3,4,137,145],[1,4,10,13,81,88,284,523,640]),([0,1,2,3,4,9,123],[0,6,186,202,350]),([0,1,2,3,4,123,126],[0,6,202,350]),([0,1,2,3,4,123,218],[6,10,202,350]),([0,1,2,3,4,343],[0,1,6,7,10,11,81,86,274]),([0,1,2,3,4,166],[0,1,6,10,13,81,664]),([0,1,2,3,4,87,189],[0,1,5,12,13,21,125,390]),([0,1,2,3,4,44,55],[0,1,12,23,25,665]),([0,1,3,4,44,87,111],[5,12,22,103,130,316,372]),([0,1,2,4,14,44,87],[5,12,22,60,130,316,378]),([0,1,2,3,4,51,87],[0,5,10,12,22,81,124,316,392]),([0,1,2,3,4,44,90],[0,12,23,124,130,666]),([0,1,2,3,4,144,321],[1,22,23,546,617]),([0,1,2,3,4,153,321],[1,22,546,617]),([0,1,2,3,4,170,321],[22,124,546,617]),([0,1,2,3,4,380],[0,4,13,22,124,667]),([0,1,3,4,111,321],[7,10,22,124,546,668]),([0,1,2,4,14,321],[7,22,81,124,378,617]),([0,1,2,3,4,322],[0,1,22,669]),([0,1,2,3,4,87,340],[0,1,4,12,13,24,46,581]),([0,1,3,4,55,87,111],[4,13,22,130,178,540,557]),([0,1,2,4,14,55,87],[4,13,22,130,157,540,566]),([0,1,2,3,4,56,87],[1,4,10,13,22,81,124,540,583]),([0,1,2,3,4,55,90],[1,13,25,124,130,670]),([0,1,2,3,4,172,285],[0,22,25,363,451]),([0,1,2,3,4,172,293],[0,22,363,451]),([0,1,2,3,4,172,319],[22,124,363,451]),([0,1,2,3,4,379],[0,1,5,12,21,22,124,389]),([0,1,3,4,111,172],[6,10,22,124,363,671]),([0,1,2,4,14,172],[6,22,81,124,451,566]),([0,1,2,3,4,173],[0,1,22,672]),([0,1,3,4,18,87,111],[7,12,33,97,137,292,365]),([0,1,3,4,87,336],[5,10,33,81,554,673]),([0,1,3,4,33,87,111],[6,13,33,97,195,521,549]),([0,1,3,4,87,186],[4,10,33,81,370,674]),([0,1,14,87,111],[10,22,33,51,81,88,97,124,130,205,675]),([0,1,2,4,14,87,224],[5,7,51,88,145,293,455]),([0,1,2,4,87,323],[10,12,81,88,562,676,677,678]),([0,1,2,4,14,87,88],[4,6,51,88,201,523,620]),([0,1,2,4,87,174],[10,13,81,88,376,679,680,681]),([0,1,2,3,4,28,90],[0,524]),([0,1,2,3,4,332],[0,1,22,33,88,212,383,683,684,685]),([0,1,2,3,4,90,332],[0,22,33,88,212]),([0,1,2,3,4,19,90],[1,212,571]),([0,1,2,3,4,181],[0,1,22,33,88,368,524,686,687,688])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_12 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_12 = true := by decide +kernel
def h26Block6_13 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,90,181],[1,22,33,88,524]),([0,1,2,3,4,87,332],[0,12,33,46,88,124,212,683]),([0,1,2,3,4,87,181],[1,13,33,88,124,125,524,686]),([0,1,2,3,4,333],[0,1,5,10,12,22,81,215,689,690,691]),([0,1,2,3,4,182],[0,1,4,10,13,22,81,552,692,693,694]),([0,1,2,3,4,90],[0,1,22,212,213,524]),([0,1,2,3,4,111,176],[0,1,7,12,13,32,82,402]),([0,1,2,3,4,18,33],[0,1,12,34,36,695]),([0,1,2,3,14,18,111],[7,12,33,72,97,292,381]),([0,1,2,3,4,61,111],[0,7,10,12,22,81,97,292,404]),([0,1,2,3,4,18,90],[0,12,34,81,214,696]),([0,1,2,3,4,84,336],[1,33,34,554,625]),([0,1,2,3,4,121,336],[1,33,554,625]),([0,1,2,3,4,143,336],[33,81,554,625]),([0,1,2,3,4,398],[0,6,13,33,81,697]),([0,1,2,3,14,336],[5,33,81,124,381,625]),([0,1,2,3,4,337],[0,1,22,33,698]),([0,1,2,3,4,111,326],[0,1,6,12,13,35,49,594]),([0,1,2,3,14,33,111],[6,13,33,97,167,521,569]),([0,1,2,3,4,62,111],[1,6,10,13,22,81,97,521,596]),([0,1,2,3,4,33,90],[1,13,36,81,214,699]),([0,1,2,3,4,186,219],[0,33,36,370,458]),([0,1,2,3,4,186,238],[0,33,370,458]),([0,1,2,3,4,186,284],[33,81,370,458]),([0,1,2,3,4,397],[0,1,7,12,32,33,81,401]),([0,1,2,3,14,186],[4,33,81,124,458,569]),([0,1,2,3,4,187],[0,1,22,33,700]),([0,1,2,3,14,111,224],[5,7,51,88,112,293,460]),([0,1,2,3,111,323],[10,12,88,124,563,678,701,702]),([0,1,2,3,14,88,111],[4,6,51,88,186,523,628]),([0,1,2,3,111,174],[10,13,88,124,377,679,703,704]),([0,1,2,3,4,111,332],[0,12,22,49,81,88,212,683]),([0,1,2,3,4,111,181],[1,13,22,81,82,88,524,686]),([0,1,2,3,4,341],[0,1,7,10,12,33,81,226,705,706,707]),([0,1,2,3,4,190],[0,1,6,10,13,33,81,559,708,709,710]),([0,1,2,3,4,88,224],[0,1,5,89,91,711]),([0,1,2,3,4,14,177],[0,1,4,5,7,8]),([0,1,2,3,4,90,224],[0,5,10,91,213,712]),([0,1,2,3,4,14,133],[0,5,7,10,22,51]),([0,1,2,3,4,424],[0,4,6,10,88,561,713,714,715]),([0,1,2,3,4,365],[0,1,22,33,88,678,716,717,718]),([0,1,2,3,4,14,327],[0,1,4,5,6,9]),([0,1,2,3,4,88,90],[1,4,10,89,213,719]),([0,1,2,3,4,14,137],[1,4,6,10,22,51,523,641]),([0,1,2,3,4,423],[0,1,5,7,10,88]),([0,1,2,3,4,276],[0,1,22,33,88,679,720,721,722]),([0,1,2,3,4,14,332],[0,5,9,10,22,33,212,684]),([0,1,2,3,4,14,181],[1,4,8,10,22,33,524,687]),([0,1,2,3,4,362],[0,1,5,7,10,88,247,723,724,725]),([0,1,2,3,4,271],[0,1,4,6,10,88,565,726,727,728])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test6_13 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Block6_13 = true := by decide +kernel
def h26Nodes6 : List NodeSpec := h26Block6_0 ++ h26Block6_1 ++ h26Block6_2 ++ h26Block6_3 ++ h26Block6_4 ++ h26Block6_5 ++ h26Block6_6 ++ h26Block6_7 ++ h26Block6_8 ++ h26Block6_9 ++ h26Block6_10 ++ h26Block6_11 ++ h26Block6_12 ++ h26Block6_13
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Check6 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket5 6 h26Nodes6 = true := by
  unfold h26Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h26Test6_0,h26Test6_1⟩,h26Test6_2⟩,h26Test6_3⟩,h26Test6_4⟩,h26Test6_5⟩,h26Test6_6⟩,h26Test6_7⟩,h26Test6_8⟩,h26Test6_9⟩,h26Test6_10⟩,h26Test6_11⟩,h26Test6_12⟩,h26Test6_13⟩
def h26Bucket6 : BT (List (List Nat)) := buildBucketsBT h26W h26Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G 6 xs.toFinset) h26Bucket6 := buildBucketsBT_sound (by decide) h26Pairs h26WOk h26PoolsOk h26AutosOk h26Bucket5Ok h26Check6
def h26Block7_0 : List NodeSpec := nodesWithIdentity [([1,2,3,4,6,10],[0,1,2,10,11,12,19,38,42]),([1,2,3,4,6,220],[0,1,5,11,76,77,81,85,93]),([1,2,3,4,6,286],[0,1,7,11,116,117,120,124,128]),([0,2,3,4,6,12],[0,1,10,11,13,19,26,78,118]),([0,2,3,4,6,85],[0,1,4,11,37,39,81,85,121]),([0,2,3,4,6,145],[0,1,6,11,41,43,92,124,128]),([0,1,2,3,4,6,87],[0,1,10,11,19,22,46,81,85,125,128,130]),([0,1,2,3,4,6,111],[0,1,10,11,19,33,49,82,85,97,124,128]),([0,1,2,3,4,41],[2,11,12,13,26,81,124,206]),([0,1,2,3,4,6,41],[2,10,11,12,13,19,26,85,128,206]),([0,1,2,3,4,125],[0,1,11,19,81,101,102,124,136,177]),([0,1,2,3,4,6,14],[0,1,8,9,11,19,51,81,85,88,124,128]),([0,1,2,3,4,17],[4,5,10,11,16,17,18,85,124,129]),([0,1,2,3,4,6,17],[4,5,11,16,17,18,19,81,85,128,129]),([0,1,2,3,4,43],[0,1,10,11,56,57,85,124,144,154]),([0,1,2,3,4,45],[6,7,10,11,28,29,30,81,86,128]),([0,1,2,3,4,6,45],[6,7,11,19,28,29,30,85,86,124,128]),([0,1,2,3,4,47],[0,1,10,11,68,69,81,110,128,164]),([1,2,3,4,10,220],[0,5,10,12,81,98,103,281,286]),([1,2,3,4,10,286],[0,7,10,12,124,133,137,305,308]),([0,1,3,4,10,12],[0,1,2,10,12,13,26,280,304]),([0,1,2,3,4,10,85],[0,1,2,4,10,12,39,81,103,137,201,307]),([0,1,2,3,4,10,145],[0,1,2,6,10,12,43,103,124,137,284,285]),([0,1,2,3,4,10,41],[1,2,11,12,13,26,103,137,206]),([0,1,2,3,4,171],[0,1,2,10,12,81,124,288,289,311,356]),([0,1,3,4,10,87],[0,10,12,22,45,46,81,103,313]),([0,1,3,4,10,111],[0,10,12,33,48,49,124,137,294]),([0,1,2,3,4,10,14],[0,2,8,9,10,12,51,81,88,103,124,137]),([0,1,2,3,4,44],[1,5,12,21,22,23,60,103,124,316]),([0,1,2,3,4,10,44],[2,5,12,21,22,23,60,81,103,137,316]),([0,1,2,3,4,54],[0,1,10,12,61,63,103,124,321,327]),([0,1,2,3,4,18],[1,7,12,32,33,34,72,81,137,292]),([0,1,2,3,4,10,18],[2,7,12,32,33,34,72,103,124,137,292]),([0,1,2,3,4,32],[0,1,10,12,73,75,81,137,300,334]),([1,2,3,4,220,286],[0,5,7,81,124,145,412,414,415]),([0,1,2,3,4,12,220],[0,1,5,10,13,26,76,81,145,178,195,281]),([0,1,2,4,85,220],[0,1,4,5,39,76,81,283,416]),([0,1,2,3,4,145,220],[0,1,5,6,43,76,81,124,145,281,284,285]),([0,1,2,3,4,17,220],[1,4,5,11,16,17,18,76,85,129,145,281]),([0,1,2,3,4,178],[0,1,5,10,17,81,124,290,449]),([0,1,2,4,87,220],[0,5,10,22,46,81,95,281,419]),([0,1,2,3,4,111,220],[0,5,10,33,49,76,81,82,97,124,145,281]),([0,1,2,3,4,44,220],[5,10,12,21,22,23,60,76,103,145,281,316]),([0,1,2,3,4,134],[0,1,5,10,60,81,104,124,434]),([0,1,2,4,14,220],[0,5,9,81,88,105,124,145,296]),([0,1,2,3,4,224],[1,5,7,10,88,90,91,112,145,293]),([0,1,2,3,4,220,224],[5,7,76,88,90,91,112,124,145,281,293]),([0,1,2,3,4,225],[0,1,5,10,81,113,115,145,302,427]),([0,1,2,3,4,12,286],[0,1,7,10,13,26,116,124,178,195,305,414]),([0,1,2,3,4,85,286],[0,1,4,7,39,81,116,124,201,305,307,414]),([0,1,2,3,145,286],[0,1,6,7,43,116,124,309,418]),([0,1,2,3,4,45,286],[1,6,7,11,28,29,30,86,116,128,305,414]),([0,1,2,3,4,175],[0,1,7,10,29,81,124,312,489]),([0,1,2,3,4,87,286],[0,7,10,22,46,81,116,124,125,130,305,414]),([0,1,2,3,111,286],[0,7,10,33,49,124,131,305,421]),([0,1,2,3,4,18,286],[7,10,12,32,33,34,72,116,137,292,305,414]),([0,1,2,3,4,132],[0,1,7,10,72,81,124,138,482]),([0,1,2,3,14,286],[0,7,9,81,88,124,139,317,414]),([0,1,2,3,4,224,286],[5,7,81,88,90,91,112,116,145,293,305,414]),([0,1,2,3,4,239],[0,1,7,10,81,112,124,146,474]),([0,1,2,3,4,12,41],[0,2,11,12,13,26,178,195,206]),([0,1,2,3,4,320],[0,1,10,13,26,81,124,504,505,508,511]),([0,2,3,4,12,85],[1,4,10,13,81,173,178,307,518]),([0,2,3,4,12,145],[1,6,10,13,124,192,195,284,535]),([0,1,3,4,12,87],[1,10,13,22,81,125,147,178,537]),([0,1,3,4,12,111],[1,10,13,33,82,124,149,195,525]),([0,1,2,3,4,12,14],[1,8,9,10,13,26,51,81,88,124,178,195]),([0,1,2,3,4,55],[0,4,13,22,24,25,124,157,178,540]),([0,1,2,3,4,12,55],[4,13,22,24,25,26,81,157,178,195,540]),([0,1,2,3,4,59],[0,1,10,13,124,158,160,178,330,545])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test7_0 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket6 7 h26Block7_0 = true := by decide +kernel
def h26Block7_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,33],[0,6,13,33,35,36,81,167,195,521]),([0,1,2,3,4,12,33],[6,13,26,33,35,36,124,167,178,195,521]),([0,1,2,3,4,38],[0,1,10,13,81,168,170,195,337,531]),([0,1,2,3,4,17,85],[0,4,5,11,16,17,18,39,85,129,201,307]),([0,1,2,3,4,328],[0,1,4,10,18,81,124,519,606]),([0,2,3,4,85,145],[1,4,6,81,124,201,285,339,609]),([0,1,2,4,85,87],[1,4,10,22,81,125,171,307,611]),([0,1,2,3,4,85,111],[1,4,10,33,39,49,81,82,97,124,201,307]),([0,1,2,3,4,55,85],[4,10,13,22,24,25,39,157,178,201,307,540]),([0,1,2,3,4,127],[0,1,4,10,81,124,157,179,432]),([0,1,2,4,14,85],[1,4,8,81,88,124,180,201,527]),([0,1,2,3,4,88],[0,4,6,10,87,88,89,186,201,523]),([0,1,2,3,4,85,88],[4,6,39,87,88,89,124,186,201,307,523]),([0,1,2,3,4,89],[0,1,4,10,81,187,189,201,344,533]),([0,1,2,3,4,45,145],[0,6,7,11,28,29,30,43,86,128,284,285]),([0,1,2,3,4,324],[0,1,6,10,30,81,124,536,648]),([0,1,2,3,4,87,145],[1,6,10,22,43,46,81,124,125,130,284,285]),([0,1,2,3,111,145],[1,6,10,33,82,124,190,284,613]),([0,1,2,3,4,33,145],[6,10,13,33,35,36,43,167,195,284,285,521]),([0,1,2,3,4,160],[0,1,6,10,81,124,167,196,441]),([0,1,2,3,14,145],[1,6,8,81,88,124,197,285,541]),([0,1,2,3,4,88,145],[4,6,43,81,87,88,89,186,201,284,285,523]),([0,1,2,3,4,123],[0,1,6,10,81,124,186,202,350]),([0,1,2,3,4,44,87],[0,5,12,21,22,23,46,60,103,125,130,316]),([0,1,2,3,4,321],[0,1,10,22,23,81,124,546,617]),([0,1,2,3,4,55,87],[1,4,13,22,24,25,46,125,130,157,178,540]),([0,1,2,3,4,172],[0,1,10,22,25,81,124,363,451]),([0,1,3,4,87,111],[10,22,33,81,97,124,130,204,618]),([0,1,2,4,14,87],[10,22,51,81,88,124,130,208,547]),([0,1,2,3,4,90],[0,1,22,33,88,130,212,213,214,524]),([0,1,2,3,4,87,90],[22,33,46,88,124,125,130,212,213,214,524]),([0,1,2,3,4,94],[0,1,10,22,81,130,215,216,217,552]),([0,1,2,3,4,18,111],[0,7,12,32,33,34,49,72,82,97,137,292]),([0,1,2,3,4,336],[0,1,10,33,34,81,124,554,625]),([0,1,2,3,4,33,111],[1,6,13,33,35,36,49,82,97,167,195,521]),([0,1,2,3,4,186],[0,1,10,33,36,81,124,370,458]),([0,1,2,3,14,111],[10,33,51,81,88,97,124,224,555]),([0,1,2,3,4,90,111],[22,33,49,81,82,88,97,130,212,213,214,524]),([0,1,2,3,4,122],[0,1,10,33,81,97,124,226,227,228,559]),([0,1,2,3,4,14,224],[0,5,7,8,9,51,88,90,91,112,145,293]),([0,1,2,3,4,323],[0,1,9,10,81,88,124,561,562,563,678]),([0,1,2,3,4,14,88],[1,4,6,8,9,51,87,88,89,186,201,523]),([0,1,2,3,4,174],[0,1,8,10,81,88,124,246,376,377,679]),([0,1,2,3,4,14,90],[8,9,10,22,33,51,88,130,212,213,214,524]),([0,1,2,3,4,130],[0,1,10,51,81,88,124,247,248,249,565])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test7_1 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket6 7 h26Block7_1 = true := by decide +kernel
def h26Nodes7 : List NodeSpec := h26Block7_0 ++ h26Block7_1
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Check7 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket6 7 h26Nodes7 = true := by
  unfold h26Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h26Test7_0,h26Test7_1⟩
def h26Bucket7 : BT (List (List Nat)) := buildBucketsBT h26W h26Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G 7 xs.toFinset) h26Bucket7 := buildBucketsBT_sound (by decide) h26Pairs h26WOk h26PoolsOk h26AutosOk h26Bucket6Ok h26Check7
def h26Block8_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,6],[0,1,10,11,19,81,85,124,128]),([0,1,2,3,4,10],[0,1,2,10,12,81,103,124,137]),([0,1,2,3,4,220],[0,1,5,10,76,81,124,145,281]),([0,1,2,3,4,286],[0,1,7,10,81,116,124,305,414]),([0,1,2,3,4,12],[0,1,10,13,26,81,124,178,195]),([0,1,2,3,4,85],[0,1,4,10,39,81,124,201,307]),([0,1,2,3,4,145],[0,1,6,10,43,81,124,284,285]),([0,1,2,3,4,87],[0,1,10,22,46,81,124,125,130]),([0,1,2,3,4,111],[0,1,10,33,49,81,82,97,124]),([0,1,2,3,4,14],[0,1,8,9,10,51,81,88,124])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test8_0 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket7 8 h26Block8_0 = true := by decide +kernel
def h26Nodes8 : List NodeSpec := h26Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Check8 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket7 8 h26Nodes8 = true := h26Test8_0
def h26Bucket8 : BT (List (List Nat)) := buildBucketsBT h26W h26Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G 8 xs.toFinset) h26Bucket8 := buildBucketsBT_sound (by decide) h26Pairs h26WOk h26PoolsOk h26AutosOk h26Bucket7Ok h26Check8
def h26Block9_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,1,10,81,124])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Test9_0 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket8 9 h26Block9_0 = true := by decide +kernel
def h26Nodes9 : List NodeSpec := h26Block9_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Check9 : checkNodesBT h26W h26G h26Mask h26Pools h26Autos h26Bucket8 9 h26Nodes9 = true := h26Test9_0
def h26Bucket9 : BT (List (List Nat)) := buildBucketsBT h26W h26Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h26G 9 xs.toFinset) h26Bucket9 := buildBucketsBT_sound (by decide) h26Pairs h26WOk h26PoolsOk h26AutosOk h26Bucket8Ok h26Check9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 10 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 3,2,10),(VAR 4,2,18),(VAR 5,2,34)]) (by decide +kernel) h26Bucket9Ok (by decide +kernel)
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xeeeaeaa8eaa8e880eeeaeaa8eaa8e880
def h0Pos : List Nat := [13,14,7,7,11,14,7,14,11,54,19,19,54,35,35,11,13,7,13,21,30,37,46,21,37,25,25,41,41,11,49,54,58,19,30,46,30,46]
def h0Neg : List Nat := [12,12,5,6,10,10,3,6,3,38,3,18,22,3,34,9,9,1,5,5,28,5,44,17,33,9,17,9,33,1,48,50,50,17,26,42,22,38]
def h0Mask : Nat := fullMask 38
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x27fafed5d,0x23fafa544),(0xcccccccccccccccccccccccccccccccc,0x3fa052fffe,0x3d80007ff8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3c81ff12ef,0x30007c128f),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3d3e5581b3,0xc0a518033),(0xffff0000ffff0000ffff0000ffff0000,0x17c6981e00,0x17c4901800),(0xffffffff00000000ffffffff00000000,0x29d9607200,0x29d1404200)]
def h0Steps : List (Nat × Nat × Nat) := [(2,1,2),(2,1,3),(1,2,3),(0,0,8)]
def h0W : BT Decor := buildWiresBT 4 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[]]
def h0Autos : BT (List (Nat × Nat)) := btOfList 1 h0AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Pairs : goodPairs h0G h0Pos h0Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0BaseOk : ∀ x ∈ h0Base, faithful h0Pos h0Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0WOk : btAll (fun x => faithful h0Pos h0Neg x ∧ x.1 < 2^128) h0W := buildWiresBT_faithful h0BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h0G = h0G) h0Autos := btAll_ofList (autos_of (by decide +kernel))
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,10),some (subcubeFast 0 2,9),some (subcubeFast 0 4,8),some (subcubeFast 0 8,8),some (subcubeFast 0 16,9),some (subcubeFast 0 32,9),some (subcubeFast 2 0,8),some (subcubeFast 2 1,7),some (subcubeFast 4 0,9),some (subcubeFast 8 0,9),some (subcubeFast 16 0,9),some (subcubeFast 32 0,9)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 4 h0SliceList
def h0Specs : List PoolSpec := [(0,[]),(8,[]),(1,[]),(0,[(2,1,2)]),(6,[]),(7,[]),(9,[(2,1,2)]),(4,[(2,1,2)]),(10,[(2,1,2)]),(5,[(2,1,2)]),(11,[(2,1,2)]),(9,[]),(3,[]),(10,[]),(4,[]),(11,[]),(5,[]),(0,[(2,1,3)]),(8,[(2,1,3)]),(4,[(2,1,3)]),(10,[(2,1,3)]),(5,[(2,1,3)]),(11,[(2,1,3)]),(2,[]),(0,[(1,2,3)]),(1,[(1,2,3)]),(10,[(1,2,3)]),(4,[(1,2,3)]),(11,[(1,2,3)]),(5,[(1,2,3)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 5 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 32 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 16 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 8 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 4 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 2 1) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 2 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 32) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 16) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 8) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 10 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (9 - 1) xs.toFinset) h0Empty := trivial
def h0Block9_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,9],[0,1,2,4,11,13,14,15,16,23,24])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 9 h0Block9_0 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 9 h0Nodes9 = true := h0Test9_0
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check9
def h0Block10_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,6],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]),([0,1,2,3,4,5,7],[0,1,2,4,5,11,13,14,15,16,17,18,19,20,21,22,23]),([0,1,2,3,4,5,8],[0,1,2,4,11,13,14,15,16,23,24,25,26,27,28,29])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Nodes10 : List NodeSpec := h0Block10_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Nodes10 = true := h0Test10_0
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket9Ok h0Check10
def h0Block11_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5],[0,1,2,11,13,14,15,16])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test11_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket10 11 h0Block11_0 = true := by decide +kernel
def h0Nodes11 : List NodeSpec := h0Block11_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket10 11 h0Nodes11 = true := h0Test11_0
def h0Bucket11 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 11 xs.toFinset) h0Bucket11 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket10Ok h0Check11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,6,7),(VAR 1,5,7),(VAR 2,3,7),(VAR 3,3,11),(VAR 4,3,19),(VAR 5,3,35)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 13]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4008372904 * 2 ^ 32 + 3936938112) ||| ((4008372904 * 2 ^ 32 + 3936938112) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4008372904 * 2 ^ 32 + 3936938112) ||| ((4008372904 * 2 ^ 32 + 3936938112) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_48478
theorem PEqualNP.Outside.L_meta_48478 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372904 * 2 ^ 32 + 3936938112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372904 * 2 ^ 32 + 3936938112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_48478.table2_of_lower (4008372904 * 2 ^ 32 + 3936938112) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_48478.low_root
    PEqualNP.Outside.L_meta_48478.wit PEqualNP.Outside.L_meta_48478.wo (by decide)
    PEqualNP.Outside.L_meta_48478.wit_mono PEqualNP.Outside.L_meta_48478.wit_eval s hcs
