import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_46856
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
def hashWs (nb : Nat) (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) % nb
def bucketContains (buckets : Array (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (buckets.getD (hashWs buckets.size s) []).contains s
def closeChild (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContains prevBuckets (ws.map (permWord sw)))
lemma closeChild_sound {raw T pools autos prevBuckets k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T k xs.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChild pools autos prevBuckets k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContains at hhit
    simp only [Array.getD, List.contains_eq_mem, decide_eq_true_eq] at hhit
    split at hhit
    next hlt_b =>
      have himp := hPrev _ hlt_b _ hhit
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
        · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
              Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
      have hfix_r : permWord sw.reverse T = T := by
        conv_lhs => rw [← hfix]
        exact hinv_w T hT
      have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [permWord_eq_renameW sw hsv x (hlt x hx)]
        exact renameW_lt _ x
      have hrot := rotate_impossible himp sw.reverse hvr hT hfix_r hmap_lt
      have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
        exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
      rwa [hback] at hrot
    next => simp at hhit
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
def evalMove (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild pools autos prevBuckets (cap - 1) rest (d, a.1, b.1)
def testPair (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMove cap n fmask ws cov pools autos prevBuckets d a b z
  go false false && go true false && go false true && go true true
def testAll (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPair cap n fmask ws cov pools autos prevBuckets a b)) &&
      testAll cap n fmask ws cov pools autos prevBuckets bs
lemma evalMove_sound {raw T pos neg ws pools autos prevBuckets cap a b d ka kb}
    (hT : T < 2^128)
    (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (hd : d < 4)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (hnz : (dbin d a b).1 ≠ 0) (hfr : (dbin d a b).1 ∉ ws.map Prod.fst)
    (test : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets
      d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => hfr ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
      exact hlt w (sub.subset hw)
  have hfr_b : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
    exact hfr (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    change _ = (z.1 :: rest.map Prod.fst).length
    rw [List.length_cons, List.length_map, delTwo_len ws a b ka kb ha hb ne, Nat.add_comm 1]
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
  unfold evalMove at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  exact closeChild_sound (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT hPools hAutos hPrev ndc hltc test k hk h
lemma testAll_pair {cap n fmask ws cov pools autos prevBuckets l}
    (h : testAll cap n fmask ws cov pools autos prevBuckets l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets a b d = true) ∨
    (∀ d < 4, testPair cap n fmask ws cov pools autos prevBuckets b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAll, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma node_sound {raw T pos neg ws pools autos prevBuckets cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (cap - 1) xs.toFinset)
    (checks : cap = 0 ∨ testAll cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0; intro k hk h
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
      (ht : testPair cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMove cap ws.length (fullMask pos.length) ws (coverage ws) pools autos prevBuckets d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPair, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMove_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAll_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
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
lemma lower_of_forest {roots T cap} {topBuckets : Array (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : ∀ i (hi : i < topBuckets.size), ∀ xs ∈ topBuckets[i], Impossible T cap xs.toFinset)
    (hRoot : bucketContains topBuckets roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContains Array.getD at hRoot
    dsimp only at hRoot
    split at hRoot
    next hi => exact hTop _ hi _ (List.contains_iff_mem.mp hRoot)
    next => simp at hRoot
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def buildWires (base : List Decor) (steps : List (Nat × Nat × Nat)) : Array Decor :=
  steps.foldl (fun arr s =>
    let a := arr.getD s.2.1 (0, 0, 0)
    let b := arr.getD s.2.2 (0, 0, 0)
    arr.push (dbin s.1 a b)) base.toArray
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma buildWires_faithful {pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    ∀ x ∈ (buildWires base steps).toList, faithful pos neg x ∧ x.1 < 2^128 := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hstep : ∀ (arr : Array Decor) (s : Nat × Nat × Nat),
      (∀ x ∈ arr.toList, faithful pos neg x ∧ x.1 < 2^128) →
      ∀ x ∈ (arr.push (dbin s.1 (arr.getD s.2.1 (0, 0, 0)) (arr.getD s.2.2 (0, 0, 0)))).toList,
        faithful pos neg x ∧ x.1 < 2^128 := by
    intro arr s harr x hx
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact harr x hx
    · have hget (i : Nat) : faithful pos neg (arr.getD i (0, 0, 0)) ∧ (arr.getD i (0, 0, 0)).1 < 2^128 := by
        unfold Array.getD
        split
        next hi => exact harr arr[i] (Array.getElem_mem_toList hi)
        next => exact hdef
      exact ⟨faithful_bin s.1 (hget s.2.1).1 (hget s.2.2).1, bin_lt s.1 _ _ (hget s.2.1).2 (hget s.2.2).2⟩
  unfold buildWires
  have hinit : ∀ x ∈ base.toArray.toList, faithful pos neg x ∧ x.1 < 2^128 := by simpa using hbase
  clear hbase
  generalize base.toArray = acc at hinit ⊢
  induction steps generalizing acc with
  | nil => exact hinit
  | cons s ss ih => exact ih _ (hstep acc s hinit)
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
lemma array_forall_of_list {α : Type} {P : α → Prop} {l : List α} (h : ∀ x ∈ l, P x) :
    ∀ i (hi : i < l.toArray.size), P l.toArray[i] :=
  fun i hi => h l.toArray[i] (Array.getElem_mem_toList hi)
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)

def sliceSpec (raw : List Nat) (target : Nat) (o : Option (Nat × Nat)) : Prop :=
  ∀ pair, o = some pair → Slice raw target pair.1 pair.2
lemma sliceSpecCons {raw target d k xs} (head : Slice raw target d k)
    (tail : ∀ o ∈ xs, sliceSpec raw target o) :
    ∀ o ∈ some (d,k) :: xs, sliceSpec raw target o :=
  forall_cons (fun _ eq => by cases eq; exact head) tail
lemma sliceSpecNil {raw target} : ∀ o ∈ [], sliceSpec raw target o :=
  fun _ h => (List.not_mem_nil h).elim

def poolSteps (steps : List (Nat × Nat × Nat)) (rows : List (Nat × List Nat)) : List PoolSpec :=
  let table := steps.toArray
  rows.map (fun row => (row.1, row.2.map (fun i => table[i]?.getD (0,0,0))))

abbrev NodeSpec := List Nat × List Nat × List Nat

def readIndexMask : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | fuel+1, base, bits =>
      if bits = 0 then [] else
      let zeros := (bits ^^^ (bits-1)).log2
      let index := base + zeros
      index :: readIndexMask fuel (index+1) (bits >>> (zeros+1))
def readIndexGaps : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | fuel+1, start, bits =>
      if bits ≤ 1 then [] else
      let width := (bits ^^^ (bits-1)).log2
      let tail := bits >>> (width+1)
      let gap := (1 <<< width) + (tail &&& ((1 <<< width)-1))
      (start+gap-1) :: readIndexGaps fuel (start+gap) (tail >>> width)
def decodeIndices (n : Nat) : List Nat :=
  let data := n >>> 1
  if n.testBit 0 then readIndexGaps (data.log2+1) 0 data
  else readIndexMask (data.log2+1) 0 data
def indexPairNodes (rows : List (Nat × Nat)) : List NodeSpec :=
  rows.map fun row => (decodeIndices row.1, decodeIndices row.2, [0])
def indexTripleNodes (rows : List (Nat × Nat × Nat)) : List NodeSpec :=
  rows.map fun row => (decodeIndices row.1, decodeIndices row.2.1, decodeIndices row.2.2)

def nodesWithIdentity (entries : List (List Nat × List Nat)) : List NodeSpec :=
  entries.map (fun entry => (entry.1, entry.2, [0]))

def buildPools (W : Array Decor) (raw : List Nat) (slices : Array (Nat × Nat))
    (pspecs : List PoolSpec) : Array (Option BoundPool) :=
  (pspecs.map fun (slIdx, chIdxs) =>
    match slices[slIdx]? with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
      materialize raw cs dom lb).toArray
lemma buildPools_sound {W : Array Decor} {raw T} {slices : Array (Nat × Nat)} {pspecs : List PoolSpec}
    (hSlices : ∀ i (hi : i < slices.size), Slice raw T slices[i].1 slices[i].2) :
    ∀ i (hi : i < (buildPools W raw slices pspecs).size),
      ∀ c, (buildPools W raw slices pspecs)[i] = some c → ValidPool raw T c := by
  intro i hi c hc
  unfold buildPools at hi hc
  have hmem : some c ∈ pspecs.map (fun (slIdx, chIdxs) =>
      match slices[slIdx]? with
      | none => none
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (W.getD ia (0, 0, 0)).1, (W.getD ib (0, 0, 0)).1)
        materialize raw cs dom lb) := by
    rw [← hc]
    exact Array.getElem_mem_toList hi
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp hmem
  cases hget_sl : slices[slIdx]? with
  | none => simp [hget_sl] at hmat
  | some sl =>
    simp only [hget_sl] at hmat
    have ⟨hsi, hval⟩ := Array.getElem?_eq_some_iff.mp hget_sl
    exact materialize_sound (hval ▸ hSlices slIdx hsi) hmat
def checkNode (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  let vals := ws.map Prod.fst
  let pools := ns.2.1.filterMap fun pIdx => poolTable.getD pIdx none
  let nodeAutos := ns.2.2.filterMap fun aIdx => autosTable[aIdx]?
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAll k ws.length fmask ws (coverage ws) pools nodeAutos prevBuckets ws)
def checkNodes (W : Array Decor) (T fmask : Nat)
    (poolTable : Array (Option BoundPool)) (autosTable : Array (List (Nat × Nat)))
    (prevBuckets : Array (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNode W T fmask poolTable autosTable prevBuckets k)
lemma checkNode_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (ok : checkNode W T (fullMask pos.length) poolTable autosTable prevBuckets k ns = true) :
    Impossible T k ((ns.1.map fun idx => (W.getD idx (0, 0, 0)).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (W.getD idx (0, 0, 0)) ∧ (W.getD idx (0, 0, 0)).1 < 2^128 := by
    unfold Array.getD; split
    next hi => exact hW W[idx] (Array.getElem_mem_toList hi)
    next => exact hdef
  unfold checkNode at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => W.getD idx (0, 0, 0)
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (W.getD idx (0, 0, 0)).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply node_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun c hc => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hc
      unfold Array.getD at hmat
      split at hmat
      next hi => exact hPoolTable pIdx hi c hmat
      next => simp at hmat)
    (fun sw hsw => by
      obtain ⟨aIdx, _, ha⟩ := List.mem_filterMap.mp hsw
      have ⟨hi, hval⟩ := Array.getElem?_eq_some_iff.mp ha
      exact hAutos sw (hval ▸ Array.getElem_mem_toList hi))
    hPrev ok.2
def nodeVals (W : Array Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (W.getD idx (0, 0, 0)).1)
def insertBucket (buckets : Array (List (List Nat))) (xs : List Nat) : Array (List (List Nat)) :=
  let idx := hashWs buckets.size xs
  if h : idx < buckets.size then
    let b := buckets[idx]
    if b.contains xs then buckets else buckets.set idx (xs :: b) h
  else buckets
def buildBuckets (nb : Nat) (W : Array Decor) (nodes : List NodeSpec) : Array (List (List Nat)) :=
  nodes.foldl (fun acc ns => insertBucket acc (nodeVals W ns)) (Array.replicate nb [])
lemma insertBucket_mem {bks : Array (List (List Nat))} {P : List Nat → Prop} {xs : List Nat}
    (hb : ∀ i (hi : i < bks.size), ∀ ys ∈ bks[i], P ys) (hxs : P xs) :
    ∀ i (hi : i < (insertBucket bks xs).size), ∀ ys ∈ (insertBucket bks xs)[i], P ys := by
  unfold insertBucket
  dsimp only
  split
  next hidx =>
    split
    · exact hb
    · intro i hi ys hys
      rw [Array.size_set] at hi
      rw [Array.getElem_set] at hys
      split at hys
      next =>
        rcases List.mem_cons.mp hys with rfl | hys'
        · exact hxs
        · exact hb _ hidx ys hys'
      next => exact hb i hi ys hys
  next => exact hb
lemma buildBuckets_sound {W : Array Decor} {raw pos neg T poolTable autosTable prevBuckets k nb}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : ∀ x ∈ W.toList, faithful pos neg x ∧ x.1 < 2^128)
    (hPoolTable : ∀ i (hi : i < poolTable.size), ∀ c, poolTable[i] = some c → ValidPool raw T c)
    (hAutos : ∀ sw ∈ autosTable.toList, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : ∀ i (hi : i < prevBuckets.size), ∀ xs ∈ prevBuckets[i], Impossible T (k - 1) xs.toFinset)
    (hNodes : checkNodes W T (fullMask pos.length) poolTable autosTable prevBuckets k nodes = true) :
    ∀ i (hi : i < (buildBuckets nb W nodes).size), ∀ xs ∈ (buildBuckets nb W nodes)[i], Impossible T k xs.toFinset := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeVals W ns).toFinset := fun ns hns => by
    unfold nodeVals
    rw [sortNats_toFinset]
    exact checkNode_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBuckets
  have hinit : ∀ i (hi : i < (Array.replicate nb ([] : List (List Nat))).size),
      ∀ xs ∈ (Array.replicate nb ([] : List (List Nat)))[i], Impossible T k xs.toFinset := by
    intro i hi xs hxs; simp at hxs
  generalize Array.replicate nb ([] : List (List Nat)) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    exact ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      (insertBucket acc (nodeVals W ns)) (insertBucket_mem hinit (hmem ns (List.mem_cons_self ..)))
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
def startDecor (roots pos neg : List Nat) : List Decor :=
  roots.map fun x => (x, projBits pos x, projBits neg x)
def startWires (roots pos neg : List Nat) : BT Decor :=
  buildWiresBT 4 (startDecor roots pos neg) []
def startNodes (roots : List Nat) : List NodeSpec := [(List.range roots.length, [], [0])]
def singleLayerCheck (roots : List Nat) (T k : Nat) (pos neg : List Nat)
    (essentialPairs : List (Nat × Nat × Nat)) : Bool :=
  forestRootCheck roots T essentialPairs && decide (T < 2^128) &&
  goodPairsCheck T pos neg && baseCheck pos neg (startDecor roots pos neg) &&
  checkNodesBT (startWires roots pos neg) T (fullMask pos.length)
    BT.empty BT.empty BT.empty k (startNodes roots) &&
  bucketContainsBT (buildBucketsBT (startWires roots pos neg) (startNodes roots)) roots
lemma lower_from_single_layer {roots T k pos neg essentialPairs}
    (h : singleLayerCheck roots T k pos neg essentialPairs = true) :
    Lower roots T (k+1) := by
  simp only [singleLayerCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hr,hT⟩,hp⟩,hb⟩,hn⟩,hm⟩ := h
  apply lower_of_forestBT hr _ hm
  apply buildBucketsBT_sound (raw := roots) hT (goodPairs_of hp) _ _ _ _ hn
  · exact buildWiresBT_faithful (base_of hb)
  · trivial
  · trivial
  · trivial
def identifyRow (i j keep : Nat) (r : Row) : Row :=
  let x := r.val &&& keep
  ⟨(if x.testBit j then x ||| (2^i) else x) % 128, Nat.mod_lt _ (by decide)⟩
lemma mapped_slice {raw : List Nat} {T d : Nat} {roots : List Nat} {G cost : Nat}
    (f : Row → Row) (hd : ∀ r : Row, d.testBit (f r).val = true)
    (hc : raw.all (fun a => freeIn roots (renameW f a)) = true)
    (ht : renameW f T = G) (proper : checkProper G = true)
    (low : Lower roots G cost) : Slice raw T d cost := by
  obtain ⟨ne, lt, bit⟩ := checkProper_sound proper
  have eq : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs ht)
  refine ⟨f, roots, hd, ?_, ?_, ?_⟩
  · exact fun a ha => freeIn_sound (List.all_eq_true.mp hc a ha)
  · rw [eq]
    exact obs_not_const ne lt bit
  · rw [eq]
    exact low
def oppositeRow (i j keep : Nat) (r : Row) : Row :=
  let x := r.val &&& keep
  ⟨(if x.testBit j then x else x ||| (2^i)) % 128, Nat.mod_lt _ (by decide)⟩
def freeSigned (roots : List Nat) (w : Nat) : Bool :=
  freeIn roots w || roots.any (fun b => w == (ALL128 ^^^ b))
lemma freeSigned_sound {roots : List Nat} {f : Row → Row} {a : Nat}
    (ok : freeSigned roots (renameW f a) = true) :
    Avail (roots.map obs) (restrictW f (obs a)) := by
  simp only [freeSigned, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at ok
  rcases ok with h | ⟨b, hb, heq⟩
  · exact freeIn_sound h
  · have eq : restrictW f (obs a) = invW (obs b) := by
      rw [← obs_renameW, heq]
      funext r
      have hall : ALL128.testBit r.val = true := by
        simp only [ALL128]; have h := r.isLt
        simpa [h] using Nat.testBit_two_pow_sub_one 128 r.val
      simp [obs, invW, Nat.testBit_xor, hall]
    rw [eq]
    exact avail_inv (Or.inl (List.mem_map_of_mem hb))
lemma opposite_slice {raw : List Nat} {T d : Nat} {roots : List Nat} {G cost : Nat}
    (f : Row → Row) (hd : ∀ r : Row, d.testBit (f r).val = true)
    (hc : raw.all (fun a => freeSigned roots (renameW f a)) = true)
    (ht : renameW f T = G) (proper : checkProper G = true)
    (low : Lower roots G cost) : Slice raw T d cost := by
  obtain ⟨ne, lt, bit⟩ := checkProper_sound proper
  have eq : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs ht)
  refine ⟨f, roots, hd, ?_, ?_, ?_⟩
  · exact fun a ha => freeSigned_sound (List.all_eq_true.mp hc a ha)
  · rw [eq]; exact obs_not_const ne lt bit
  · rw [eq]; exact low
def h3R : List Nat := varsOf 44
def h3G : Nat := 0xfff0fff0f000f000fff0fff0f000f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 4 := lower_from_single_layer (k := 3) (pos := [36,40,12,12,40,36]) (neg := [32,32,4,8,8,4]) (essentialPairs := [(VAR 2,8,12),(VAR 3,4,12),(VAR 5,4,36)]) (by decide +kernel)
def h4R : List Nat := varsOf 13
def h4G : Nat := 0xfa0afa0afa0afa0afa0afa0afa0afa0a
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 3 := lower_from_single_layer (k := 2) (pos := [1,1,12,9]) (neg := [0,5,8,8]) (essentialPairs := [(VAR 0,0,1),(VAR 2,1,5),(VAR 3,4,12)]) (by decide +kernel)
def h6R : List Nat := varsOf 36
def h6G : Nat := 0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 3 := lower_from_single_layer (k := 2) (pos := [4,32,4,32]) (neg := [0,0,36,36]) (essentialPairs := [(VAR 2,0,4),(VAR 5,0,32)]) (by decide +kernel)
def h5R : List Nat := varsOf 44
def h5G : Nat := 0xf000f00f000f0000f000f00f000f000
lemma h5Bound : Lower h5R h5G 4 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,4,12)]) (by decide +kernel) h6Bound
def h7R : List Nat := varsOf 37
def h7G : Nat := 0xafafafaffafafafaafafafaffafafafa
lemma h7Bound : Lower h7R h7G 4 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h6Bound
def h8R : List Nat := varsOf 41
def h8G : Nat := 0xaaaaaaaaff00ff00aaaaaaaaff00ff00
lemma h8Bound : Lower h8R h8G 3 := carry_of (swaps := [(2,3),(3,4),(4,5),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h2R : List Nat := varsOf 45
def h2G : Nat := 0xafaaafaafa0afa0aafaaafaafa0afa0a
def h2Pos : List Nat := [1,12,1,37,12,9,13,12,37,40,40,40]
def h2Neg : List Nat := [0,8,5,36,4,8,5,44,5,32,8,44]
def h2Mask : Nat := fullMask 12
def h2Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,365,324),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,474,2524),(0xff00ff00ff00ff00ff00ff00ff00ff00,3826,3234),(0xffffffff00000000ffffffff00000000,3848,2696)]
def h2Steps : List (Nat × Nat × Nat) := [(2,1,3)]
def h2W : BT Decor := buildWiresBT 3 h2Base h2Steps
def h2AutoList : List (List (Nat × Nat)) := [[]]
def h2Autos : BT (List (Nat × Nat)) := btOfList 1 h2AutoList
lemma h2Pairs : goodPairs h2G h2Pos h2Neg := goodPairs_of (by decide +kernel)
lemma h2BaseOk : ∀ x ∈ h2Base, faithful h2Pos h2Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h2WOk : btAll (fun x => faithful h2Pos h2Neg x ∧ x.1 < 2^128) h2W := buildWiresBT_faithful h2BaseOk
lemma h2AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h2G = h2G) h2Autos := btAll_ofList (autos_of (by decide +kernel))
def h2SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,3),some (subcubeFast 0 8,4),some (subcubeFast 1 0,4),some (subcubeFast 32 0,3),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,4)]
def h2Slices : BT (Option (Nat × Nat)) := btOfList 3 h2SliceList
def h2Specs : List PoolSpec := [(2,[]),(1,[]),(3,[]),(0,[]),(4,[])]
def h2Pools : BT (Option BoundPool) := buildPoolsBT 3 h2W h2R h2Slices h2Specs
set_option maxRecDepth 200000 in
lemma h2Slice4 : Slice h2R h2G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 4 := mapped_slice (identifyRow 0 2 44) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h2Slice3 : Slice h2R h2G (subcubeFast 32 0) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
lemma h2Slice2 : Slice h2R h2G (subcubeFast 1 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
lemma h2Slice1 : Slice h2R h2G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
lemma h2Slice0 : Slice h2R h2G (subcubeFast 0 4) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
lemma h2SlicesOk : btAll (sliceSpec h2R h2G) h2Slices := btAll_ofList (P := sliceSpec h2R h2G) (sliceSpecCons h2Slice0 (sliceSpecCons h2Slice1 (sliceSpecCons h2Slice2 (sliceSpecCons h2Slice3 (sliceSpecCons h2Slice4 sliceSpecNil)))))
lemma h2PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h2R h2G c) h2Pools := buildPoolsBT_sound h2SlicesOk
def h2Empty : BT (List (List Nat)) := BT.empty
lemma h2EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h2G (4 - 1) xs.toFinset) h2Empty := trivial
def h2Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,3,4])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Test4_0 : checkNodesBT h2W h2G h2Mask h2Pools h2Autos h2Empty 4 h2Block4_0 = true := by decide +kernel
def h2Nodes4 : List NodeSpec := h2Block4_0
lemma h2Check4 : checkNodesBT h2W h2G h2Mask h2Pools h2Autos h2Empty 4 h2Nodes4 = true := h2Test4_0
def h2Bucket4 : BT (List (List Nat)) := buildBucketsBT h2W h2Nodes4
lemma h2Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h2G 4 xs.toFinset) h2Bucket4 := buildBucketsBT_sound (by decide) h2Pairs h2WOk h2PoolsOk h2AutosOk h2EmptyOk h2Check4
def h2Block5_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Test5_0 : checkNodesBT h2W h2G h2Mask h2Pools h2Autos h2Bucket4 5 h2Block5_0 = true := by decide +kernel
def h2Nodes5 : List NodeSpec := h2Block5_0
lemma h2Check5 : checkNodesBT h2W h2G h2Mask h2Pools h2Autos h2Bucket4 5 h2Nodes5 = true := h2Test5_0
def h2Bucket5 : BT (List (List Nat)) := buildBucketsBT h2W h2Nodes5
lemma h2Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h2G 5 xs.toFinset) h2Bucket5 := buildBucketsBT_sound (by decide) h2Pairs h2WOk h2PoolsOk h2AutosOk h2Bucket4Ok h2Check5
lemma h2Bound : Lower h2R h2G 6 := lower_of_forestBT (essPairs := [(VAR 0,0,1),(VAR 2,1,5),(VAR 3,4,12),(VAR 5,5,37)]) (by decide +kernel) h2Bucket5Ok (by decide +kernel)
def h10R : List Nat := varsOf 42
def h10G : Nat := 0xcc00cc00ffccffcccc00cc00ffccffcc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 4 := lower_from_single_layer (k := 3) (pos := [2,8,42,42,8,2]) (neg := [0,0,34,40,40,34]) (essentialPairs := [(VAR 1,0,2),(VAR 3,0,8),(VAR 5,2,34)]) (by decide +kernel)
def h9R : List Nat := varsOf 46
def h9G : Nat := 0xccc0ccc0ffccffccccc0ccc0ffccffcc
lemma h9Bound : Lower h9R h9G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,34,38)]) (by decide +kernel) h10Bound
def h11R : List Nat := varsOf 46
def h11G : Nat := 0xccfcccfcf0ccf0ccccfcccfcf0ccf0cc
lemma h11Bound : Lower h11R h11G 6 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h13R : List Nat := varsOf 14
def h13G : Nat := 0xf3c0f3c0f3c0f3c0f3c0f3c0f3c0f3c0
lemma h13Bound : Lower h13R h13G 3 := carry_of (swaps := [(0,1),(1,2),(2,3)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h12R : List Nat := varsOf 46
def h12G : Nat := 0xfff0fff0f3c0f3c0fff0fff0f3c0f3c0
def h12Pos : List Nat := [8,36,6,6,8,42,36,42,12,14]
def h12Neg : List Nat := [10,32,2,4,0,34,4,10,4,10]
def h12Mask : Nat := fullMask 10
def h12Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,684,677),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,846,328),(0xff00ff00ff00ff00ff00ff00ff00ff00,945,641),(0xffffffff00000000ffffffff00000000,226,34)]
def h12Steps : List (Nat × Nat × Nat) := []
def h12W : BT Decor := buildWiresBT 2 h12Base h12Steps
def h12AutoList : List (List (Nat × Nat)) := [[]]
def h12Autos : BT (List (Nat × Nat)) := btOfList 1 h12AutoList
lemma h12Pairs : goodPairs h12G h12Pos h12Neg := goodPairs_of (by decide +kernel)
lemma h12BaseOk : ∀ x ∈ h12Base, faithful h12Pos h12Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h12WOk : btAll (fun x => faithful h12Pos h12Neg x ∧ x.1 < 2^128) h12W := buildWiresBT_faithful h12BaseOk
lemma h12AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h12G = h12G) h12Autos := btAll_ofList (autos_of (by decide +kernel))
def h12SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 32 0,3)]
def h12Slices : BT (Option (Nat × Nat)) := btOfList 1 h12SliceList
def h12Specs : List PoolSpec := [(0,[])]
def h12Pools : BT (Option BoundPool) := buildPoolsBT 1 h12W h12R h12Slices h12Specs
set_option maxRecDepth 200000 in
lemma h12Slice0 : Slice h12R h12G (subcubeFast 32 0) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
lemma h12SlicesOk : btAll (sliceSpec h12R h12G) h12Slices := btAll_ofList (P := sliceSpec h12R h12G) (sliceSpecCons h12Slice0 sliceSpecNil)
lemma h12PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h12R h12G c) h12Pools := buildPoolsBT_sound h12SlicesOk
def h12Empty : BT (List (List Nat)) := BT.empty
lemma h12EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h12G (4 - 1) xs.toFinset) h12Empty := trivial
def h12Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Test4_0 : checkNodesBT h12W h12G h12Mask h12Pools h12Autos h12Empty 4 h12Block4_0 = true := by decide +kernel
def h12Nodes4 : List NodeSpec := h12Block4_0
lemma h12Check4 : checkNodesBT h12W h12G h12Mask h12Pools h12Autos h12Empty 4 h12Nodes4 = true := h12Test4_0
def h12Bucket4 : BT (List (List Nat)) := buildBucketsBT h12W h12Nodes4
lemma h12Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h12G 4 xs.toFinset) h12Bucket4 := buildBucketsBT_sound (by decide) h12Pairs h12WOk h12PoolsOk h12AutosOk h12EmptyOk h12Check4
lemma h12Bound : Lower h12R h12G 5 := lower_of_forestBT (essPairs := [(VAR 1,4,6),(VAR 2,2,6),(VAR 3,0,8),(VAR 5,4,36)]) (by decide +kernel) h12Bucket4Ok (by decide +kernel)
def h15R : List Nat := varsOf 35
def h15G : Nat := 0xeeeeeeee88888888eeeeeeee88888888
lemma h15Bound : Lower h15R h15G 4 := carry_of (swaps := [(1,2),(2,3),(0,1),(1,2)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h14R : List Nat := varsOf 39
def h14G : Nat := 0xeeeeeeeec8c8c8c8eeeeeeeec8c8c8c8
lemma h14Bound : Lower h14R h14G 5 := lift_of (z := 4) (o := 0) (essPairs := [(VAR 2,2,6)]) (by decide +kernel) h15Bound
def h16R : List Nat := varsOf 43
def h16G : Nat := 0xeeeeeeeeaa88aa88eeeeeeeeaa88aa88
lemma h16Bound : Lower h16R h16G 5 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h17R : List Nat := varsOf 45
def h17G : Nat := 0xfffafffafa00fa00fffafffafa00fa00
lemma h17Bound : Lower h17R h17G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) h3Bound
def h19R : List Nat := varsOf 37
def h19G : Nat := 0xa0a0a0a0fafafafaa0a0a0a0fafafafa
lemma h19Bound : Lower h19R h19G 4 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h20R : List Nat := varsOf 41
def h20G : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
lemma h20Bound : Lower h20R h20G 4 := carry_of (swaps := [(1,2),(0,1)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h18R : List Nat := varsOf 45
def h18G : Nat := 0xffa0ffa0fa00fa00ffa0ffa0fa00fa00
def h18Pos : List Nat := [9,12,12,9,37,40,37,37,13,40,9]
def h18Neg : List Nat := [8,8,4,1,5,8,36,33,5,32,0]
def h18Mask : Nat := fullMask 11
def h18Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1497,408),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,470,340),(0xff00ff00ff00ff00ff00ff00ff00ff00,1839,35),(0xffffffff00000000ffffffff00000000,752,704)]
def h18Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,2),(3,0,2)]
def h18W : BT Decor := buildWiresBT 3 h18Base h18Steps
def h18AutoList : List (List (Nat × Nat)) := [[],[(2,5)],[(0,2)],[(0,5)],[(2,5),(0,2)],[(2,5),(0,5)]]
def h18Autos : BT (List (Nat × Nat)) := btOfList 3 h18AutoList
lemma h18Pairs : goodPairs h18G h18Pos h18Neg := goodPairs_of (by decide +kernel)
lemma h18BaseOk : ∀ x ∈ h18Base, faithful h18Pos h18Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h18WOk : btAll (fun x => faithful h18Pos h18Neg x ∧ x.1 < 2^128) h18W := buildWiresBT_faithful h18BaseOk
lemma h18AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h18G = h18G) h18Autos := btAll_ofList (autos_of (by decide +kernel))
def h18SliceList : List (Option (Nat × Nat)) := [some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,4),some (0xaaaaaaaa55555555aaaaaaaa55555555,4),some (0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0f,4),some (0x55aa55aa55aa55aa55aa55aa55aa55aa,4),some (0xff00ff00ff00ff00ff00ff00ff00ff0,4),some (0xff00ffff00ff0000ff00ffff00ff00,4)]
def h18Slices : BT (Option (Nat × Nat)) := btOfList 3 h18SliceList
def h18Specs : List PoolSpec := [(0,[]),(3,[]),(1,[]),(4,[]),(2,[]),(5,[])]
def h18Pools : BT (Option BoundPool) := buildPoolsBT 3 h18W h18R h18Slices h18Specs
set_option maxRecDepth 200000 in
lemma h18Slice5 : Slice h18R h18G (0xff00ffff00ff0000ff00ffff00ff00) 4 := opposite_slice (oppositeRow 3 5 37) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
lemma h18Slice4 : Slice h18R h18G (0xff00ff00ff00ff00ff00ff00ff00ff0) 4 := opposite_slice (oppositeRow 2 3 41) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
lemma h18Slice3 : Slice h18R h18G (0x55aa55aa55aa55aa55aa55aa55aa55aa) 4 := opposite_slice (oppositeRow 0 3 44) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h18Slice2 : Slice h18R h18G (0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0f) 4 := mapped_slice (identifyRow 2 5 41) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
lemma h18Slice1 : Slice h18R h18G (0xaaaaaaaa55555555aaaaaaaa55555555) 4 := mapped_slice (identifyRow 0 5 44) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h18Slice0 : Slice h18R h18G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 4 := mapped_slice (identifyRow 0 2 44) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h3Bound
lemma h18SlicesOk : btAll (sliceSpec h18R h18G) h18Slices := btAll_ofList (P := sliceSpec h18R h18G) (sliceSpecCons h18Slice0 (sliceSpecCons h18Slice1 (sliceSpecCons h18Slice2 (sliceSpecCons h18Slice3 (sliceSpecCons h18Slice4 (sliceSpecCons h18Slice5 sliceSpecNil))))))
lemma h18PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h18R h18G c) h18Pools := buildPoolsBT_sound h18SlicesOk
def h18Empty : BT (List (List Nat)) := BT.empty
lemma h18EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G (4 - 1) xs.toFinset) h18Empty := trivial
def h18Block4_0 : List NodeSpec := indexPairNodes [(62,2), (94,2), (158,0), (286,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Test4_0 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Empty 4 h18Block4_0 = true := by decide +kernel
def h18Nodes4 : List NodeSpec := h18Block4_0
lemma h18Check4 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Empty 4 h18Nodes4 = true := h18Test4_0
def h18Bucket4 : BT (List (List Nat)) := buildBucketsBT h18W h18Nodes4
lemma h18Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G 4 xs.toFinset) h18Bucket4 := buildBucketsBT_sound (by decide) h18Pairs h18WOk h18PoolsOk h18AutosOk h18EmptyOk h18Check4
def h18Block5_0 : List NodeSpec := [([0,1,2,3],[0,1,2,3,4,5],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Test5_0 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Bucket4 5 h18Block5_0 = true := by decide +kernel
def h18Nodes5 : List NodeSpec := h18Block5_0
lemma h18Check5 : checkNodesBT h18W h18G h18Mask h18Pools h18Autos h18Bucket4 5 h18Nodes5 = true := h18Test5_0
def h18Bucket5 : BT (List (List Nat)) := buildBucketsBT h18W h18Nodes5
lemma h18Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h18G 5 xs.toFinset) h18Bucket5 := buildBucketsBT_sound (by decide) h18Pairs h18WOk h18PoolsOk h18AutosOk h18Bucket4Ok h18Check5
lemma h18Bound : Lower h18R h18G 6 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 2,8,12),(VAR 3,1,9),(VAR 5,5,37)]) (by decide +kernel) h18Bucket5Ok (by decide +kernel)
def h21R : List Nat := varsOf 46
def h21G : Nat := 0xfffcfffcf0c0f0c0fffcfffcf0c0f0c0
lemma h21Bound : Lower h21R h21G 5 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h22R : List Nat := varsOf 46
def h22G : Nat := 0xfcf0fcf0f0c0f0c0fcf0fcf0f0c0f0c0
lemma h22Bound : Lower h22R h22G 6 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h23R : List Nat := varsOf 7
def h23G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
lemma h23Bound : Lower h23R h23G 4 := carry_of (swaps := [(4,5),(1,2),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h24R : List Nat := varsOf 39
def h24G : Nat := 0xe8e8e8e8c8c8c8c8e8e8e8e8c8c8c8c8
lemma h24Bound : Lower h24R h24G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,5,37)]) (by decide +kernel) h23Bound
def h25R : List Nat := varsOf 11
def h25G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
lemma h25Bound : Lower h25R h25G 4 := carry_of (swaps := [(4,5),(1,2),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h26R : List Nat := varsOf 43
def h26G : Nat := 0xee88ee88aa88aa88ee88ee88aa88aa88
lemma h26Bound : Lower h26R h26G 5 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h24R) (T2 := h24G) (by decide +kernel) h24Bound
def h27R : List Nat := varsOf 45
def h27G : Nat := 0xaaa0aaa0fa00fa00aaa0aaa0fa00fa00
def h27Pos : List Nat := [9,12,37,37,12,9,12,37,41]
def h27Neg : List Nat := [8,8,33,36,4,1,44,5,33]
def h27Mask : Nat := fullMask 9
def h27Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,429,420),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,222,216),(0xff00ff00ff00ff00ff00ff00ff00ff00,371,67),(0xffffffff00000000ffffffff00000000,396,332)]
def h27Steps : List (Nat × Nat × Nat) := []
def h27W : BT Decor := buildWiresBT 2 h27Base h27Steps
def h27AutoList : List (List (Nat × Nat)) := [[]]
def h27Autos : BT (List (Nat × Nat)) := btOfList 1 h27AutoList
lemma h27Pairs : goodPairs h27G h27Pos h27Neg := goodPairs_of (by decide +kernel)
lemma h27BaseOk : ∀ x ∈ h27Base, faithful h27Pos h27Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h27WOk : btAll (fun x => faithful h27Pos h27Neg x ∧ x.1 < 2^128) h27W := buildWiresBT_faithful h27BaseOk
lemma h27AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h27G = h27G) h27Autos := btAll_ofList (autos_of (by decide +kernel))
def h27SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,3)]
def h27Slices : BT (Option (Nat × Nat)) := btOfList 1 h27SliceList
def h27Specs : List PoolSpec := [(0,[])]
def h27Pools : BT (Option BoundPool) := buildPoolsBT 1 h27W h27R h27Slices h27Specs
set_option maxRecDepth 200000 in
lemma h27Slice0 : Slice h27R h27G (subcubeFast 0 4) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
lemma h27SlicesOk : btAll (sliceSpec h27R h27G) h27Slices := btAll_ofList (P := sliceSpec h27R h27G) (sliceSpecCons h27Slice0 sliceSpecNil)
lemma h27PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h27R h27G c) h27Pools := buildPoolsBT_sound h27SlicesOk
def h27Empty : BT (List (List Nat)) := BT.empty
lemma h27EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h27G (4 - 1) xs.toFinset) h27Empty := trivial
def h27Block4_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Test4_0 : checkNodesBT h27W h27G h27Mask h27Pools h27Autos h27Empty 4 h27Block4_0 = true := by decide +kernel
def h27Nodes4 : List NodeSpec := h27Block4_0
lemma h27Check4 : checkNodesBT h27W h27G h27Mask h27Pools h27Autos h27Empty 4 h27Nodes4 = true := h27Test4_0
def h27Bucket4 : BT (List (List Nat)) := buildBucketsBT h27W h27Nodes4
lemma h27Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h27G 4 xs.toFinset) h27Bucket4 := buildBucketsBT_sound (by decide) h27Pairs h27WOk h27PoolsOk h27AutosOk h27EmptyOk h27Check4
lemma h27Bound : Lower h27R h27G 5 := lower_of_forestBT (essPairs := [(VAR 0,8,9),(VAR 2,8,12),(VAR 3,1,9),(VAR 5,5,37)]) (by decide +kernel) h27Bucket4Ok (by decide +kernel)
def h28R : List Nat := varsOf 38
def h28G : Nat := 0xccccccccf0f0f0f0ccccccccf0f0f0f0
lemma h28Bound : Lower h28R h28G 3 := carry_of (swaps := [(2,3),(3,4),(4,5),(0,1),(1,2)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h29R : List Nat := varsOf 46
def h29G : Nat := 0xccc0ccc0f0c0f0c0ccc0ccc0f0c0f0c0
lemma h29Bound : Lower h29R h29G 5 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h27R) (T2 := h27G) (by decide +kernel) h27Bound
def h30R : List Nat := varsOf 15
def h30G : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
lemma h30Bound : Lower h30R h30G 5 := carry_of (swaps := [(4,5),(1,2),(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h31R : List Nat := varsOf 39
def h31G : Nat := 0xeeeeeeeefafafafaeeeeeeeefafafafa
lemma h31Bound : Lower h31R h31G 4 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h28Bound
def h32R : List Nat := varsOf 43
def h32G : Nat := 0xeeeeeeeeffccffcceeeeeeeeffccffcc
lemma h32Bound : Lower h32R h32G 4 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h31R) (T2 := h31G) (by decide +kernel) h31Bound
def h1R : List Nat := varsOf 47
def h1G : Nat := 0xeee8eee8fac8fac8eee8eee8fac8fac8
def h1Pos : List Nat := [6,9,6,6,37,37,12,9,12,37,3,42,42,42,3,45,46,6,12,6,37,7,35,35,11,9,6,41,38,13,41,3,7,3,11,3,35,12,14,13,12,13,37,7,12,6,14,35,38,41,9,41,38,3,41,14,12,12,37,38,37,9,42,13,35,38]
def h1Neg : List Nat := [4,8,5,2,33,36,4,1,44,5,2,40,34,10,1,44,44,10,8,34,1,5,33,34,10,10,36,44,34,5,40,0,2,10,2,34,2,5,10,4,0,44,4,4,10,0,4,32,4,33,33,1,44,33,8,8,36,40,32,2,0,40,2,8,1,36]
def h1Mask : Nat := fullMask 66
def h1Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1b46e8e9febf0c6b2,0x1002e002020704294),(0xcccccccccccccccccccccccccccccccc,0x348b1e85f95eb7c0d,0x4800105f138a3408),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x29f917fe1343f837d,0x201114ea02c218365),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xe3ce53e46b05b9c2,0xa2d012424b07a902),(0xffffffff00000000ffffffff00000000,0x35c5b841058d1ba30,0x2273682085cc99930)]
def h1Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(3,1,3),(0,1,4),(1,1,4),(3,1,4),(0,2,3),(1,0,30),(1,2,3),(2,2,3),(3,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(1,2,5),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(0,3,39),(0,4,39),(3,4,39),(2,2,5),(1,3,5),(1,4,5),(2,4,5),(2,0,50),(2,1,50),(0,2,50),(2,2,50),(1,5,30),(1,0,35),(1,1,35),(1,3,35),(2,3,35),(3,35,48),(1,5,59),(1,5,35),(1,0,37),(0,1,63),(1,1,63),(2,1,63),(3,1,63),(2,0,37),(1,1,37),(1,5,37),(0,0,45),(2,3,45),(2,3,53),(0,2,6),(3,2,6),(0,3,9),(3,3,9),(0,4,6),(2,4,6),(3,4,6),(0,4,9),(2,4,9),(0,6,9),(0,6,25),(0,9,25),(3,1,9),(1,1,33),(2,6,33),(2,9,33),(0,4,57),(0,1,58),(3,1,58),(0,4,58),(2,4,58),(1,1,78),(2,9,35),(2,6,35),(1,1,74),(1,1,79),(1,1,10),(1,3,10),(1,4,10),(2,4,10),(2,6,10),(1,1,11),(1,3,11),(2,4,75),(3,1,13),(3,2,13),(0,4,13),(1,0,110),(0,1,110),(1,1,110),(2,1,110),(3,1,110),(0,2,110),(1,2,110),(2,2,110),(3,2,110),(1,3,110),(3,4,13),(1,1,15),(1,2,15),(3,1,17),(1,0,78),(1,2,19),(1,3,19),(3,1,31),(2,6,30),(3,0,32),(3,1,32),(1,0,93),(3,0,93),(1,2,93),(3,4,32),(0,6,32),(1,0,33),(3,1,56),(3,0,57),(3,0,36),(3,1,36),(0,6,36),(2,6,37),(1,1,107),(3,1,107),(1,0,79),(1,1,80),(1,3,7),(2,4,7),(1,7,35),(1,2,7),(3,0,21),(0,4,152),(3,4,21),(1,0,26),(1,2,26),(0,4,148),(3,0,28),(1,7,30),(1,7,34),(0,4,151),(3,7,36),(1,1,162),(1,7,37),(1,1,161),(3,0,134),(2,2,40),(1,0,167),(1,7,40),(1,1,42),(1,7,42),(1,3,8),(1,8,24),(3,1,172),(0,4,172),(1,8,26),(1,2,16),(2,9,40),(2,9,29),(2,9,93),(0,9,32),(3,19,32),(1,19,43),(2,9,26),(1,1,184),(1,2,179),(3,0,87),(2,9,38),(1,2,77),(2,4,77),(1,10,29),(3,1,101),(0,4,101),(0,3,103),(2,3,103),(1,10,26),(1,10,40),(2,3,145),(1,1,198),(2,4,109),(3,11,21),(1,11,26),(3,1,202),(0,2,84),(1,2,84),(2,2,84),(3,2,84),(2,1,12),(2,2,12),(1,4,12),(3,20,183),(1,12,20),(0,21,183),(1,12,90),(3,12,21),(1,12,22),(2,4,204),(0,4,205),(0,21,110),(1,2,219),(2,21,110),(0,13,21),(2,13,22),(2,4,108),(2,13,27),(2,13,29),(2,13,35),(2,2,112),(1,1,14),(2,4,14),(1,14,22),(1,14,27),(0,4,232),(1,1,230),(1,14,29),(0,4,189),(1,14,35),(0,4,123),(1,16,42),(3,1,120),(2,17,29),(2,2,18),(1,3,52),(3,0,69),(1,19,37),(3,1,41),(3,1,127),(1,3,64),(3,3,65)]
def h1W : BT Decor := buildWiresBT 8 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[],[(2,3),(0,1)]]
def h1Autos : BT (List (Nat × Nat)) := btOfList 1 h1AutoList
lemma h1Pairs : goodPairs h1G h1Pos h1Neg := goodPairs_of (by decide +kernel)
lemma h1BaseOk : ∀ x ∈ h1Base, faithful h1Pos h1Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h1WOk : btAll (fun x => faithful h1Pos h1Neg x ∧ x.1 < 2^128) h1W := buildWiresBT_faithful h1BaseOk
lemma h1AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h1G = h1G) h1Autos := btAll_ofList (autos_of (by decide +kernel))
def h1SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,4),some (subcubeFast 0 8,4),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 8,3),some (subcubeFast 2 0,5),some (subcubeFast 2 4,3),some (subcubeFast 4 0,5),some (subcubeFast 4 32,4),some (subcubeFast 8 0,5),some (subcubeFast 8 32,4),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,6),some (0xaaaaaaaa55555555aaaaaaaa55555555,5),some (0xcc33cc33cc33cc33cc33cc33cc33cc33,6),some (0xcccccccc33333333cccccccc33333333,5),some (0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0f,5),some (0xff00ff0000ff00ffff00ff0000ff00ff,5),some (0x66666666666666666666666666666666,5),some (0x55aa55aa55aa55aa55aa55aa55aa55aa,6),some (0x55555555aaaaaaaa55555555aaaaaaaa,5),some (0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c,6)]
def h1Slices : BT (Option (Nat × Nat)) := btOfList 5 h1SliceList
def h1Specs : List PoolSpec := poolSteps h1Steps [(3,[]),(5,[]),(7,[]),(9,[]),(8,[]),(11,[]),(13,[]),(4,[]),(6,[]),(1,[]),(10,[]),(2,[54]),(2,[]),(19,[]),(0,[]),(16,[]),(15,[]),(11,[1]),(17,[]),(9,[116]),(12,[]),(20,[]),(18,[]),(14,[]),(11,[2]),(7,[85]),(13,[1]),(3,[35]),(3,[37]),(11,[93]),(11,[167]),(3,[170]),(11,[167,170]),(7,[170]),(9,[105]),(11,[11]),(7,[14]),(7,[88]),(11,[27]),(2,[53]),(11,[14]),(11,[16]),(11,[18]),(2,[27]),(16,[4]),(11,[28]),(2,[28]),(11,[30]),(11,[30,53]),(11,[33]),(7,[77]),(7,[98]),(7,[97]),(20,[6]),(16,[6]),(5,[30]),(3,[105]),(3,[116]),(9,[233]),(9,[11]),(7,[35]),(7,[37]),(7,[12]),(9,[24]),(12,[238]),(9,[30]),(5,[32]),(9,[32]),(7,[130]),(9,[130]),(13,[27]),(7,[135])]
def h1Pools : BT (Option BoundPool) := buildPoolsBT 7 h1W h1R h1Slices h1Specs
set_option maxRecDepth 200000 in
lemma h1Slice20 : Slice h1R h1G (0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c) 6 := opposite_slice (oppositeRow 1 2 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
lemma h1Slice19 : Slice h1R h1G (0x55555555aaaaaaaa55555555aaaaaaaa) 5 := opposite_slice (oppositeRow 0 5 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
lemma h1Slice18 : Slice h1R h1G (0x55aa55aa55aa55aa55aa55aa55aa55aa) 6 := opposite_slice (oppositeRow 0 3 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
lemma h1Slice17 : Slice h1R h1G (0x66666666666666666666666666666666) 5 := opposite_slice (oppositeRow 0 1 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
lemma h1Slice16 : Slice h1R h1G (0xff00ff0000ff00ffff00ff0000ff00ff) 5 := mapped_slice (identifyRow 3 5 39) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
lemma h1Slice15 : Slice h1R h1G (0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0f) 5 := mapped_slice (identifyRow 2 5 43) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
lemma h1Slice14 : Slice h1R h1G (0xcccccccc33333333cccccccc33333333) 5 := mapped_slice (identifyRow 1 5 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
lemma h1Slice13 : Slice h1R h1G (0xcc33cc33cc33cc33cc33cc33cc33cc33) 6 := mapped_slice (identifyRow 1 3 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
lemma h1Slice12 : Slice h1R h1G (0xaaaaaaaa55555555aaaaaaaa55555555) 5 := mapped_slice (identifyRow 0 5 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
lemma h1Slice11 : Slice h1R h1G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 6 := mapped_slice (identifyRow 0 2 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
lemma h1Slice10 : Slice h1R h1G (subcubeFast 8 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
lemma h1Slice9 : Slice h1R h1G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
lemma h1Slice8 : Slice h1R h1G (subcubeFast 4 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
lemma h1Slice7 : Slice h1R h1G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
lemma h1Slice6 : Slice h1R h1G (subcubeFast 2 4) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
lemma h1Slice5 : Slice h1R h1G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
lemma h1Slice4 : Slice h1R h1G (subcubeFast 1 8) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
lemma h1Slice3 : Slice h1R h1G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
lemma h1Slice2 : Slice h1R h1G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
lemma h1Slice1 : Slice h1R h1G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
lemma h1Slice0 : Slice h1R h1G (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
lemma h1SlicesOk : btAll (sliceSpec h1R h1G) h1Slices := btAll_ofList (P := sliceSpec h1R h1G) (sliceSpecCons h1Slice0 (sliceSpecCons h1Slice1 (sliceSpecCons h1Slice2 (sliceSpecCons h1Slice3 (sliceSpecCons h1Slice4 (sliceSpecCons h1Slice5 (sliceSpecCons h1Slice6 (sliceSpecCons h1Slice7 (sliceSpecCons h1Slice8 (sliceSpecCons h1Slice9 (sliceSpecCons h1Slice10 (sliceSpecCons h1Slice11 (sliceSpecCons h1Slice12 (sliceSpecCons h1Slice13 (sliceSpecCons h1Slice14 (sliceSpecCons h1Slice15 (sliceSpecCons h1Slice16 (sliceSpecCons h1Slice17 (sliceSpecCons h1Slice18 (sliceSpecCons h1Slice19 (sliceSpecCons h1Slice20 sliceSpecNil)))))))))))))))))))))
set_option maxRecDepth 200000 in
lemma h1PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h1R h1G c) h1Pools := buildPoolsBT_sound h1SlicesOk
def h1Empty : BT (List (List Nat)) := BT.empty
lemma h1EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G (4 - 1) xs.toFinset) h1Empty := trivial
def h1Block4_0 : List NodeSpec := indexPairNodes [(85997623,0), (462895,0), (4997647,0), (471087,0), (130228309,0), (281032759,0), (24658447,0), (5210301,256), (25434441,0), (25958757,0), (5839850021,0), (20473359,0), (105308325,0), (32622645,0), (30737238565,256), (275779855,0), (313528591,0), (5570093079,0), (4999906889,0), (1250019877,0), (4798450213,0), (4999776805,12993), (363859109,0), (1292012069,0), (662782085,1945617), (5201103397,0), (5242489381,1697), (136374389285,0), (86983838245,249873), (5872242711,4929), (1447035957,0), (1602300943,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test4_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 4 h1Block4_0 = true := by decide +kernel
def h1Block4_1 : List NodeSpec := indexPairNodes [(6476304427,0), (1132585287,0), (1699901,0), (6744576053,0), (1708063,0), (4597092413,0), (27406379,0), (1724447,0), (1732639,0), (17918210091,0), (18052427819,0), (1773599,0), (1789983,0), (7415885847,0), (7952756759,0), (1963290677,0), (338231298085,0), (73553281671,5185), (4932718615,0), (89124254471,0), (24897839189,0), (25032056917,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test4_1 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 4 h1Block4_1 = true := by decide +kernel
def h1Nodes4 : List NodeSpec := h1Block4_0 ++ h1Block4_1
lemma h1Check4 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 4 h1Nodes4 = true := by
  unfold h1Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h1Test4_0,h1Test4_1⟩
def h1Bucket4 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes4
set_option maxRecDepth 200000 in
lemma h1Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 4 xs.toFinset) h1Bucket4 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1EmptyOk h1Check4
def h1Block5_0 : List NodeSpec := indexPairNodes [(10004567,0), (10759711,0), (211007,192), (2422871,256), (14219311,337), (893103,4120), (16253983,320), (239679,1106), (958709,26696), (2633815,66), (48246831,2), (14160927,867), (544831,66), (11563095,0), (13660247,256), (15757399,66), (170047,65616), (949279,256), (2391071,867), (2165949,256), (12858021,0), (13906597,0), (137376421,0), (36439669,0), (36963957,64), (35916405,0), (36440693,64), (12910965,0), (33820247,0), (3424479,256), (3784927,43089), (16125215,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_0 = true := by decide +kernel
def h1Block5_1 : List NodeSpec := indexPairNodes [(835957,64), (190883927,0), (1028159,0), (2867423,768), (8487135,0), (2170943,768), (34472309,64), (692287,0), (3309941,64), (3375467,2), (3440943,0), (3506479,401), (182453279,1377), (766015,0), (2269247,0), (3768693,64), (645935191,0), (174068767,0), (2285631,2), (847935,365065), (2334783,0), (610367,0), (13899429,256), (147326581,0), (38142837,0), (10944671,1512497), (38666399,0), (38929269,0), (1027631151,0), (39715701,0), (254813727,0), (36569973,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_1 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_1 = true := by decide +kernel
def h1Block5_2 : List NodeSpec := indexPairNodes [(803701,0), (2547775,0), (2564159,0), (3244917,0), (977336407,256), (3441455,0), (960496671,320), (2400319,0), (35259243,433), (2596927,0), (3703669,0), (943723551,2), (2629695,64), (2580543,0), (13697909,0), (16712535,0), (42074967,0), (2711615,1057), (42861419,128), (2744383,8196), (1265695,337), (2515007,0), (2777151,0), (2457888815,0), (2826303,0), (2793535,0), (1413151,29496401), (13304479,208977), (4326452,0), (45352565,0), (51438901,0), (5243956,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_2 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_2 = true := by decide +kernel
def h1Block5_3 : List NodeSpec := indexPairNodes [(44123445,4801), (47449717,0), (226823333,141337), (276990501,76613235), (14428736677,5313), (205604149,4801), (1048659253,4801), (138495255,322), (21366039,1512497), (42731095,0), (667711,448), (253782123,497), (2957375,4), (241211499,433), (2875455,580), (22152471,507259153), (44303959,92307851), (41158231,0), (42206807,0), (12715607,497), (46826775,497), (6488887,1220559257), (45876823,64), (629182511,497), (174074911,1377), (2859071,8), (2973759,497), (3055679,8), (2646079,1377), (44091189,0), (46926453,0), (633366575,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_3 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_3 = true := by decide +kernel
def h1Block5_4 : List NodeSpec := indexPairNodes [(162536991,0), (3153983,0), (156248607,18615849), (3072063,66), (266349599,18615849), (3170367,72), (3088447,0), (3104831,8), (696403999,0), (713181215,74455057), (3070380063,2326625), (3103934495,512), (2302015,64), (51646039,0), (52166943,0), (83362327,47345), (3028293719,32), (13879095,0), (152571479,0), (3252287,0), (63180375,0), (86508055,18802039825), (3268671,0), (149947509,108), (685770271,2322), (3416127,8384), (589300853,497), (266344555,2432), (681576991,369), (41157407,31996145), (3465279,803), (262154347,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_4 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_4 = true := by decide +kernel
def h1Block5_5 : List NodeSpec := indexTripleNodes [(677383711,0,2), (3481663,130,2), (257964139,64,2), (673190431,0,2), (16173506667,2194,2), (16307724395,2434,2), (16441942123,0,2), (16576159851,0,2), (187697695,0,2), (3579967,433,2), (185601567,208977,2), (3596351,0,2), (717240427,497,2), (183505439,0,2), (235932789,4,6), (175120927,3023319073,6), (3629119,433,2), (170928671,128,6), (3645503,433,2), (3612735,0,2), (633340959,237921,2), (3661887,8200,2), (608181279,64,2), (3219519,8,2), (964639,0,2), (2799647,2949569,6), (3848223,0,2), (9615391,208977,2), (11712543,0,6), (13809695,2949569,2), (15906847,0,2), (35829791,7361,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_5 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_5 = true := by decide +kernel
def h1Block5_6 : List NodeSpec := indexTripleNodes [(40024095,0,2), (897087,1377,2), (3727423,0,2), (233837685,0,2), (3743807,0,2), (845163039,128,2), (3792959,0,2), (3760191,0,2), (2592143447,337,2), (3279946783,65600,2), (3825727,8,2), (3809343,8,2), (3776575,0,2), (1929247,178281489,2), (229647477,0,2), (547366005,0,2), (2753055,2,2), (232795167,256,2), (224410655,0,2), (1937439,33047577,2), (3874879,0,2), (891300383,0,2), (63083643957,0,2), (3021210677,0,2), (941636655,65029,6), (156238367,7656049193,2), (2924607,433,2), (40370719,0,2), (196495279127,433,2), (20710159,1945617,2), (52953631,512,2), (950010399,2,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_6 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_6 = true := by decide +kernel
def h1Block5_7 : List NodeSpec := indexTripleNodes [(954204703,0,2), (924844575,0,2), (3989567,1377,2), (1019967,0,2), (662808607,6167569,2), (679585823,119656465,2), (1392726039,3827176497,2), (2105407,1377,2), (370719,3827174481,2), (3006527,0,2), (2203711,0,2), (2220095,0,2), (36711455,0,2), (562221103,337,2), (578998319,0,6), (725055,8,2), (2613311,0,2), (1011829,26696,2), (2846837,10304,2), (3895413,0,2), (9662581,0,2), (260159,64,2), (3940415,0,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_7 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_7 = true := by decide +kernel
def h1Nodes5 : List NodeSpec := h1Block5_0 ++ h1Block5_1 ++ h1Block5_2 ++ h1Block5_3 ++ h1Block5_4 ++ h1Block5_5 ++ h1Block5_6 ++ h1Block5_7
lemma h1Check5 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Nodes5 = true := by
  unfold h1Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨h1Test5_0,h1Test5_1⟩,h1Test5_2⟩,h1Test5_3⟩,h1Test5_4⟩,h1Test5_5⟩,h1Test5_6⟩,h1Test5_7⟩
def h1Bucket5 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes5
set_option maxRecDepth 200000 in
lemma h1Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 5 xs.toFinset) h1Bucket5 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket4Ok h1Check5
def h1Block6_0 : List NodeSpec := indexTripleNodes [(104575,58,6), (125055,10506,2), (266367,10250,2), (290903,33094,6), (145471,173398,2), (356439,46,2), (95263,8230,2), (97311,774,6), (190527,231198,6), (1212,262726,2), (1214,819270,2), (2236,262982,2), (4286,557636,2), (16574,525716,2), (65726,1428,2), (94399,348615,2), (110783,697221,2), (401599,55391,6), (434367,557824,2), (450751,525402,2), (483519,532558,2), (499903,565256,2), (516287,532554,2), (1065151,2228768,2), (4489407,819268,2), (585791,173652,2), (4554943,819780,2), (610367,19104798,6), (4751551,87217,2), (618559,8008553,6), (4882623,13489,2), (1340,541391,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_0 = true := by decide +kernel
def h1Block6_1 : List NodeSpec := indexTripleNodes [(119231,33354,2), (270783,586,2), (319935,67667,2), (352703,803,6), (369087,921891,2), (190,136619974,2), (385471,138,2), (451007,82,2), (467391,8458,2), (483775,8262,2), (500159,8202,2), (516543,164458,2), (2416703,173908,2), (1098175,176347,2), (1163711,369047,2), (2367551,8496266,2), (2383935,19105054,6), (1081663,6,2), (1212735,146,2), (774207,439929775,2), (2760767,130472779,2), (17470,33904,2), (66622,33106,2), (132156,49309259,2), (689781,153230483,2), (344895,688533043,2), (820823,115428053,2), (951895,59811631,2), (1082175,34072,2), (1147711,33436,2), (1344319,18915854,2), (675903,17344198,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_1 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_1 = true := by decide +kernel
def h1Block6_2 : List NodeSpec := indexTripleNodes [(3081815,1494263165,2), (3212887,66614123,2), (3475031,2248429131,2), (3868247,1191323309,2), (2065215,40984,2), (4522815,2198552,2), (17695551,33880,2), (602175,108490,2), (17957695,32856,2), (634943,19105406,2), (19006271,2138186,2), (643135,16385254565,2), (625269,1225810579,2), (1082687,2256,2), (1279295,9985227,2), (790591,16820166,2), (1086,2139774,2), (2000191,14179421,2), (798783,107722,2), (407583,645998131,2), (411679,1191355699,2), (815167,122509774207,2), (20542,33904,2), (69694,336,2), (691799,13470123349,2), (509759,216,6), (831551,21538030,6), (2821719,747139453,2), (839743,108010,6), (2105406,2878,6), (4202558,35198,2), (8396862,32878,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_2 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_2 = true := by decide +kernel
def h1Block6_3 : List NodeSpec := indexTripleNodes [(1507903,686,2), (1319019,2194,2), (659519,16820362,6), (6701163,2070,2), (5816407,35410,2), (2908223,174684,2), (6733911,58,2), (1699871,8242,2), (1478687,2066,2), (427583,2106384,2), (4210750,35872,6), (8405054,33980,2), (1377855,1644,2), (1902143,9366,6), (4326975,3688017,6), (856127,17343626,6), (5899839,9304,2), (6686271,2237472,2), (864319,173660,2), (440351,94449745,6), (872511,6188562589343,6), (485407,1292317465,6), (8421438,70,2), (1247807,522,2), (1772095,134,2), (2034239,1514139,2), (3694655,16819338,2), (5638719,9242,2), (6425151,163946,2), (3039295,173644,2), (3711039,19106846,2), (1117759,344,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_3 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_3 = true := by decide +kernel
def h1Block6_4 : List NodeSpec := indexTripleNodes [(970815,16821642,2), (979007,174940,2), (1511999,6,6), (1774143,58247,2), (749631,18908558,6), (2842687,2262652,2), (3214111,103622674961,2), (3476255,94232484249,2), (954431,34370325658,2), (15935,619033437399,6), (822559,120067383,2), (987199,2665646,6), (2351167,44174,2), (6045783,43106,2), (7815255,10250,2), (2753055,7386433959,6), (1383999,1843655,2), (782399,19440782,6), (84418111,139719,6), (17571391,2107398,6), (1777215,2141240,2), (8651295,0xa83824126293,2), (9699871,134236619939,2), (1003583,35442487029,2), (112729663,9672101427,2), (11797023,12850491,2), (12845599,51402907,2), (1011775,2206874,2), (113778239,2105618,2), (56383,2629758,2), (1036351,2664278,6), (370719,61226464017,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_4 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_4 = true := by decide +kernel
def h1Block6_5 : List NodeSpec := indexTripleNodes [(733247,0x6a0b46264fbf,6), (64501279,122469560217,2), (129000511,175160,2), (741439,141939724249,2), (1085471,497048337,2), (217069087,123536953241,2), (2187327,2663782,2), (684095,17343662,2), (58431,0xdc18d04b7fd,2), (215103,2622582,2), (219199,139609708847,6), (2884639,0xb1990b04b19,6), (446511,205687597,6), (223295,911037846891,2), (454703,4152,6), (2236479,884834870487,6), (2252863,17346190,2), (487541,10312,2), (243775,535646,6), (1056885,10250,2), (536639,6510894159,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_5 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_5 = true := by decide +kernel
def h1Nodes6 : List NodeSpec := h1Block6_0 ++ h1Block6_1 ++ h1Block6_2 ++ h1Block6_3 ++ h1Block6_4 ++ h1Block6_5
lemma h1Check6 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Nodes6 = true := by
  unfold h1Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h1Test6_0,h1Test6_1⟩,h1Test6_2⟩,h1Test6_3⟩,h1Test6_4⟩,h1Test6_5⟩
def h1Bucket6 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes6
set_option maxRecDepth 200000 in
lemma h1Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 6 xs.toFinset) h1Bucket6 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket5Ok h1Check6
def h1Block7_0 : List NodeSpec := indexTripleNodes [(126,9182,6), (190,13115614,6), (318,8670,2), (574,8574,2), (1086,12624510,2), (2110,41854,2), (4158,8318,6), (8254,10462,2), (9791,8400094,6), (32830,8400094,6), (65598,8399070,6), (12863,10622,6), (13887,10366,6), (14911,10366,2), (15935,10496126,6), (54335,8446,6), (58431,12627966,6), (60479,9726,6), (64575,10366,6), (133183,43646,6), (137279,10334,6), (141375,4369022,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test7_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket6 7 h1Block7_0 = true := by decide +kernel
def h1Nodes7 : List NodeSpec := h1Block7_0
lemma h1Check7 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket6 7 h1Nodes7 = true := h1Test7_0
def h1Bucket7 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes7
set_option maxRecDepth 200000 in
lemma h1Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 7 xs.toFinset) h1Bucket7 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket6Ok h1Check7
def h1Block8_0 : List NodeSpec := [([0,1,2,3,4],[],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test8_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket7 8 h1Block8_0 = true := by decide +kernel
def h1Nodes8 : List NodeSpec := h1Block8_0
lemma h1Check8 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket7 8 h1Nodes8 = true := h1Test8_0
def h1Bucket8 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes8
set_option maxRecDepth 200000 in
lemma h1Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 8 xs.toFinset) h1Bucket8 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket7Ok h1Check8
set_option maxRecDepth 200000 in
lemma h1Bound : Lower h1R h1G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,2,6),(VAR 3,1,9),(VAR 5,5,37)]) (by decide +kernel) h1Bucket8Ok (by decide +kernel)
def h34R : List Nat := varsOf 53
def h34G : Nat := 0xfafaffff0000aaaafafaffff0000aaaa
lemma h34Bound : Lower h34R h34G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(1,2),(0,1)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h36R : List Nat := varsOf 52
def h36G : Nat := 0xf0f0ffff0000f0f0f0f0ffff0000f0f0
lemma h36Bound : Lower h36R h36G 4 := carry_of (swaps := [(3,4),(4,5),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h37R : List Nat := varsOf 56
def h37G : Nat := 0xffffff00ff000000ffffff00ff000000
lemma h37Bound : Lower h37R h37G 4 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h35R : List Nat := varsOf 60
def h35G : Nat := 0xf0f0fff0f000f0f0f0f0fff0f000f0f0
def h35Pos : List Nat := [4,40,4,4,40,36,12,52,40,28,12,4,28,52,60]
def h35Neg : List Nat := [0,32,8,20,56,32,8,20,8,20,0,16,24,48,56]
def h35Mask : Nat := fullMask 15
def h35Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7eed,648),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x5752,0x5154),(0xffff0000ffff0000ffff0000ffff0000,0x7280,0x7a98),(0xffffffff00000000ffffffff00000000,0x61b2,0x6032)]
def h35Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(2,3,4),(3,3,5)]
def h35W : BT Decor := buildWiresBT 4 h35Base h35Steps
def h35AutoList : List (List (Nat × Nat)) := [[],[(3,5)]]
def h35Autos : BT (List (Nat × Nat)) := btOfList 1 h35AutoList
lemma h35Pairs : goodPairs h35G h35Pos h35Neg := goodPairs_of (by decide +kernel)
lemma h35BaseOk : ∀ x ∈ h35Base, faithful h35Pos h35Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h35WOk : btAll (fun x => faithful h35Pos h35Neg x ∧ x.1 < 2^128) h35W := buildWiresBT_faithful h35BaseOk
lemma h35AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h35G = h35G) h35Autos := btAll_ofList (autos_of (by decide +kernel))
def h35SliceList : List (Option (Nat × Nat)) := [some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,4),some (0xff00ff0000ff00ffff00ff0000ff00ff,4),some (0xffff0000ffff0000ffff0000ffff00,4),some (0xffffffff00000000ffffffff0000,4)]
def h35Slices : BT (Option (Nat × Nat)) := btOfList 2 h35SliceList
def h35Specs : List PoolSpec := [(0,[]),(2,[]),(1,[]),(3,[])]
def h35Pools : BT (Option BoundPool) := buildPoolsBT 2 h35W h35R h35Slices h35Specs
set_option maxRecDepth 200000 in
lemma h35Slice3 : Slice h35R h35G (0xffffffff00000000ffffffff0000) 4 := opposite_slice (oppositeRow 4 5 44) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h35Slice2 : Slice h35R h35G (0xffff0000ffff0000ffff0000ffff00) 4 := opposite_slice (oppositeRow 3 4 52) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
lemma h35Slice1 : Slice h35R h35G (0xff00ff0000ff00ffff00ff0000ff00ff) 4 := mapped_slice (identifyRow 3 5 52) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
lemma h35Slice0 : Slice h35R h35G (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f) 4 := mapped_slice (identifyRow 2 4 56) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h37Bound
lemma h35SlicesOk : btAll (sliceSpec h35R h35G) h35Slices := btAll_ofList (P := sliceSpec h35R h35G) (sliceSpecCons h35Slice0 (sliceSpecCons h35Slice1 (sliceSpecCons h35Slice2 (sliceSpecCons h35Slice3 sliceSpecNil))))
set_option maxRecDepth 200000 in
lemma h35PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h35R h35G c) h35Pools := buildPoolsBT_sound h35SlicesOk
def h35Empty : BT (List (List Nat)) := BT.empty
lemma h35EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G (3 - 1) xs.toFinset) h35Empty := trivial
def h35Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2,14],[]),([0,1,2,15],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test3_0 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Empty 3 h35Block3_0 = true := by decide +kernel
def h35Nodes3 : List NodeSpec := h35Block3_0
lemma h35Check3 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Empty 3 h35Nodes3 = true := h35Test3_0
def h35Bucket3 : BT (List (List Nat)) := buildBucketsBT h35W h35Nodes3
set_option maxRecDepth 200000 in
lemma h35Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G 3 xs.toFinset) h35Bucket3 := buildBucketsBT_sound (by decide) h35Pairs h35WOk h35PoolsOk h35AutosOk h35EmptyOk h35Check3
def h35Block4_0 : List NodeSpec := indexPairNodes [(62,14), (94,14), (158,0), (286,0), (542,0), (1054,0), (2078,4), (4126,4), (8222,8), (5407,8)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test4_0 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket3 4 h35Block4_0 = true := by decide +kernel
def h35Nodes4 : List NodeSpec := h35Block4_0
lemma h35Check4 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket3 4 h35Nodes4 = true := h35Test4_0
def h35Bucket4 : BT (List (List Nat)) := buildBucketsBT h35W h35Nodes4
set_option maxRecDepth 200000 in
lemma h35Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G 4 xs.toFinset) h35Bucket4 := buildBucketsBT_sound (by decide) h35Pairs h35WOk h35PoolsOk h35AutosOk h35Bucket3Ok h35Check4
def h35Block5_0 : List NodeSpec := [([0,1,2,3],[0,1,2,3],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Test5_0 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket4 5 h35Block5_0 = true := by decide +kernel
def h35Nodes5 : List NodeSpec := h35Block5_0
lemma h35Check5 : checkNodesBT h35W h35G h35Mask h35Pools h35Autos h35Bucket4 5 h35Nodes5 = true := h35Test5_0
def h35Bucket5 : BT (List (List Nat)) := buildBucketsBT h35W h35Nodes5
set_option maxRecDepth 200000 in
lemma h35Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h35G 5 xs.toFinset) h35Bucket5 := buildBucketsBT_sound (by decide) h35Pairs h35WOk h35PoolsOk h35AutosOk h35Bucket4Ok h35Check5
set_option maxRecDepth 200000 in
lemma h35Bound : Lower h35R h35G 6 := lower_of_forestBT (essPairs := [(VAR 2,0,4),(VAR 3,20,28),(VAR 4,4,20),(VAR 5,8,40)]) (by decide +kernel) h35Bucket5Ok (by decide +kernel)
def h38R : List Nat := varsOf 29
def h38G : Nat := 0xfa00faaafa00faaafa00faaafa00faaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 4 := lower_from_single_layer (k := 3) (pos := [1,5,9,1,25,25,12,5]) (neg := [0,4,8,17,24,17,4,21]) (essentialPairs := [(VAR 0,0,1),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,1,17)]) (by decide +kernel)
def h39R : List Nat := varsOf 45
def h39G : Nat := 0xfffafffafaaafaaafffafffafaaafaaa
lemma h39Bound : Lower h39R h39G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h3Bound
def h40R : List Nat := varsOf 49
def h40G : Nat := 0xaaaaffff0000aaaaaaaaffff0000aaaa
lemma h40Bound : Lower h40R h40G 4 := carry_of (swaps := [(3,4),(4,5),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h41R : List Nat := varsOf 53
def h41G : Nat := 0xaaaafafa0000aaaaaaaafafa0000aaaa
lemma h41Bound : Lower h41R h41G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,32,36)]) (by decide +kernel) h40Bound
def h42R : List Nat := varsOf 57
def h42G : Nat := 0xaaaaffaaaa00aaaaaaaaffaaaa00aaaa
lemma h42Bound : Lower h42R h42G 6 := carry_of (swaps := [(1,2),(0,1)]) (roots2 := h35R) (T2 := h35G) (by decide +kernel) h35Bound
def h43R : List Nat := varsOf 28
def h43G : Nat := 0xf000fff0f000fff0f000fff0f000fff0
lemma h43Bound : Lower h43R h43G 4 := carry_of (swaps := [(4,5),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h44R : List Nat := varsOf 60
def h44G : Nat := 0xf000fff0f000f000f000fff0f000f000
lemma h44Bound : Lower h44R h44G 5 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,4,36)]) (by decide +kernel) h43Bound
def h45R : List Nat := varsOf 29
def h45G : Nat := 0xfaaafffafaaafffafaaafffafaaafffa
lemma h45Bound : Lower h45R h45G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h43Bound
def h46R : List Nat := varsOf 45
def h46G : Nat := 0xfaaafaaafa00fa00faaafaaafa00fa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 4 := lower_from_single_layer (k := 3) (pos := [9,37,9,12,12,37,33,44]) (neg := [8,36,1,4,8,5,1,36]) (essentialPairs := [(VAR 0,8,9),(VAR 2,8,12),(VAR 3,1,9),(VAR 5,1,33)]) (by decide +kernel)
def h47R : List Nat := varsOf 57
def h47G : Nat := 0xffaaffffff00ffaaffaaffffff00ffaa
lemma h47Bound : Lower h47R h47G 5 := carry_of (swaps := [(3,4),(4,5),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h33R : List Nat := varsOf 61
def h33G : Nat := 0xfaaafffafa00faaafaaafffafa00faaa
def h33Pos : List Nat := [1,12,5,12,25,1,40,36,40,36,49,53,1,25,40,36,28,5,57,37,28,28,9,60,40,60,40,33,28,28,1,5,53,49,1,5,9,9,49,28,28,29,57,25,12,36,25,49,5,25,29,1,33,40,36,40]
def h33Neg : List Nat := [0,8,4,4,17,17,56,4,8,32,17,52,8,24,32,52,20,20,56,4,21,24,17,52,48,56,0,32,8,56,4,21,21,32,32,0,8,0,48,4,52,21,17,21,0,0,56,21,17,8,17,21,17,16,20,24]
def h33Mask : Nat := fullMask 56
def h33Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x1fce7fc84e3c35,0x1d8e0180500430),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x453389b2bb8a8e,0x488b81c09b888c),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xa65fb037f5615a,0x82401032243142),(0xffff0000ffff0000ffff0000ffff0000,0x6cfc332b52c10,0xfdcf41a3f7ac70),(0xffffffff00000000ffffffff00000000,0xf0a4430f8ccfc0,0x41462b84ca40)]
def h33Steps : List (Nat × Nat × Nat) := [(1,0,1),(0,0,2),(1,0,2),(0,2,3),(1,2,3),(2,2,3),(3,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(3,2,7),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(1,2,20),(3,3,5),(1,3,7),(3,3,7),(3,3,21),(0,4,5),(0,4,7),(2,4,7),(0,4,21),(0,5,7),(0,5,21),(1,7,21),(2,2,20),(3,2,20),(0,5,20),(2,5,20),(3,2,32),(0,5,32),(2,7,20),(1,2,24),(1,2,27),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(3,0,5),(3,0,9),(1,0,20),(0,4,9),(3,4,9),(0,4,53),(3,0,20),(2,9,20),(1,0,54),(1,2,54),(1,3,54),(1,0,34),(1,3,34),(1,0,15),(2,3,15),(3,3,53),(1,15,20),(3,0,63),(3,2,63),(0,4,63),(2,4,22),(1,3,26),(3,0,21),(1,2,31),(2,0,1),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(0,1,3),(1,1,3),(3,1,3),(1,1,4),(3,1,4),(1,1,20),(1,1,22),(1,1,26),(2,7,51),(1,3,42),(2,4,42),(1,42,51),(1,9,51),(2,9,51),(1,20,51),(2,20,51),(0,4,92),(1,0,10),(1,0,70),(1,10,51),(1,0,12),(3,0,61),(1,12,51),(2,4,102),(1,15,51),(1,3,103),(2,21,51),(1,1,6),(1,3,6),(2,3,6),(1,4,6),(2,4,6),(1,2,52),(0,7,9),(3,2,64),(2,7,15),(0,1,21),(3,1,21),(1,1,16),(1,20,42),(0,2,89),(2,2,90),(1,1,43),(3,3,77),(1,0,123),(0,4,77),(3,43,77),(1,3,79),(2,4,79),(1,43,79),(1,0,84),(1,3,84),(1,2,57),(0,1,40),(1,1,40),(2,1,40),(3,1,40),(1,4,45),(2,4,45),(3,45,77),(1,45,79),(2,4,133),(1,3,76),(2,4,76),(1,4,46),(1,1,56),(2,1,56),(1,2,56),(2,2,56),(2,3,56),(3,46,77),(3,0,127),(1,46,79),(3,0,131),(1,46,84),(0,1,147),(3,1,147),(2,9,46),(1,12,46),(1,15,46),(1,56,76),(3,3,145),(0,1,41),(1,1,41),(2,1,41),(3,1,41),(1,3,47),(3,47,77),(1,47,79),(1,3,162),(1,76,149),(0,3,48),(1,1,66),(2,1,66),(1,2,66),(2,2,66),(0,48,77),(1,0,176),(1,0,128),(2,48,79),(3,0,81),(0,4,81),(1,0,181),(0,48,81),(0,9,48),(3,10,48),(0,1,174),(3,1,174),(3,15,48),(1,66,76),(0,4,172),(1,1,49),(3,49,77),(1,49,79),(3,17,77),(0,18,77),(1,2,19),(3,19,77),(3,20,77),(1,17,79),(2,18,79),(1,19,79),(1,20,79),(1,4,8),(3,1,13),(2,13,20),(2,9,17),(1,1,11),(2,1,11),(1,11,20),(2,3,14),(3,15,18)]
def h33W : BT Decor := buildWiresBT 8 h33Base h33Steps
def h33AutoList : List (List (Nat × Nat)) := [[]]
def h33Autos : BT (List (Nat × Nat)) := btOfList 1 h33AutoList
lemma h33Pairs : goodPairs h33G h33Pos h33Neg := goodPairs_of (by decide +kernel)
lemma h33BaseOk : ∀ x ∈ h33Base, faithful h33Pos h33Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h33WOk : btAll (fun x => faithful h33Pos h33Neg x ∧ x.1 < 2^128) h33W := buildWiresBT_faithful h33BaseOk
lemma h33AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h33G = h33G) h33Autos := btAll_ofList (autos_of (by decide +kernel))
def h33SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5),some (subcubeFast 0 16,4),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 4 0,6),some (subcubeFast 8 0,5),some (subcubeFast 8 4,4),some (subcubeFast 16 0,5),some (subcubeFast 17 0,4),some (subcubeFast 32 0,4),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,6),some (0xff00ff0000ff00ffff00ff0000ff00ff,5),some (0xffffffff00000000ffffffff0000,5)]
def h33Slices : BT (Option (Nat × Nat)) := btOfList 4 h33SliceList
def h33Specs : List PoolSpec := poolSteps h33Steps [(5,[]),(3,[]),(9,[]),(6,[0]),(7,[]),(4,[]),(0,[2]),(5,[2]),(8,[0]),(2,[0]),(0,[]),(5,[4]),(2,[0,48]),(0,[4]),(5,[10]),(8,[0,48]),(0,[10]),(3,[15]),(5,[15]),(5,[17]),(5,[21]),(11,[]),(6,[]),(8,[]),(1,[]),(10,[]),(2,[]),(12,[]),(5,[37]),(5,[5]),(5,[7]),(5,[1]),(5,[1,103]),(5,[1,104]),(5,[1,105]),(5,[1,106]),(8,[2]),(2,[2]),(5,[2,19]),(5,[2,22]),(6,[113]),(8,[37]),(2,[37]),(5,[38]),(5,[39]),(2,[39]),(8,[52]),(2,[52]),(5,[40]),(8,[132]),(5,[40,132]),(5,[40,133]),(8,[133]),(5,[41]),(2,[41]),(2,[48]),(5,[41,139]),(3,[139]),(5,[42]),(5,[42,161]),(2,[161]),(5,[43]),(8,[43]),(8,[48]),(5,[43,166]),(3,[166]),(5,[44]),(5,[45]),(8,[45]),(5,[118]),(5,[120]),(5,[122]),(5,[123]),(5,[175]),(5,[176]),(5,[125]),(5,[126]),(5,[3]),(5,[3,198]),(8,[47]),(5,[4,49]),(3,[12]),(8,[92]),(5,[6]),(6,[202]),(5,[8]),(0,[6]),(2,[95]),(6,[199]),(0,[8]),(5,[9]),(5,[9,205]),(2,[59]),(3,[13]),(5,[12]),(5,[13]),(5,[14]),(13,[]),(5,[14,15])]
def h33Pools : BT (Option BoundPool) := buildPoolsBT 7 h33W h33R h33Slices h33Specs
set_option maxRecDepth 200000 in
lemma h33Slice13 : Slice h33R h33G (0xffffffff00000000ffffffff0000) 5 := opposite_slice (oppositeRow 4 5 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
lemma h33Slice12 : Slice h33R h33G (0xff00ff0000ff00ffff00ff0000ff00ff) 5 := mapped_slice (identifyRow 3 5 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
lemma h33Slice11 : Slice h33R h33G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 6 := mapped_slice (identifyRow 0 2 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
lemma h33Slice10 : Slice h33R h33G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
lemma h33Slice9 : Slice h33R h33G (subcubeFast 17 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h33Slice8 : Slice h33R h33G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
lemma h33Slice7 : Slice h33R h33G (subcubeFast 8 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h40Bound
set_option maxRecDepth 200000 in
lemma h33Slice6 : Slice h33R h33G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h41Bound
set_option maxRecDepth 200000 in
lemma h33Slice5 : Slice h33R h33G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h42Bound
set_option maxRecDepth 200000 in
lemma h33Slice4 : Slice h33R h33G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h43Bound
set_option maxRecDepth 200000 in
lemma h33Slice3 : Slice h33R h33G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h44Bound
set_option maxRecDepth 200000 in
lemma h33Slice2 : Slice h33R h33G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
lemma h33Slice1 : Slice h33R h33G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
lemma h33Slice0 : Slice h33R h33G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
lemma h33SlicesOk : btAll (sliceSpec h33R h33G) h33Slices := btAll_ofList (P := sliceSpec h33R h33G) (sliceSpecCons h33Slice0 (sliceSpecCons h33Slice1 (sliceSpecCons h33Slice2 (sliceSpecCons h33Slice3 (sliceSpecCons h33Slice4 (sliceSpecCons h33Slice5 (sliceSpecCons h33Slice6 (sliceSpecCons h33Slice7 (sliceSpecCons h33Slice8 (sliceSpecCons h33Slice9 (sliceSpecCons h33Slice10 (sliceSpecCons h33Slice11 (sliceSpecCons h33Slice12 (sliceSpecCons h33Slice13 sliceSpecNil))))))))))))))
set_option maxRecDepth 200000 in
lemma h33PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h33R h33G c) h33Pools := buildPoolsBT_sound h33SlicesOk
def h33Empty : BT (List (List Nat)) := BT.empty
lemma h33EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G (3 - 1) xs.toFinset) h33Empty := trivial
def h33Block3_0 : List NodeSpec := nodesWithIdentity [([2,3,38,56],[]),([2,4,38,66],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test3_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Empty 3 h33Block3_0 = true := by decide +kernel
def h33Nodes3 : List NodeSpec := h33Block3_0
lemma h33Check3 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Empty 3 h33Nodes3 = true := h33Test3_0
def h33Bucket3 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes3
set_option maxRecDepth 200000 in
lemma h33Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 3 xs.toFinset) h33Bucket3 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33EmptyOk h33Check3
def h33Block4_0 : List NodeSpec := indexPairNodes [(475849,0), (112765,2), (282749,0), (23332013,433), (471165,0), (80750685,1057), (266365,0), (132133037,433), (115388509,1057), (112747,2), (1138811,0), (381749291,0), (1828970571,0), (1679467,0), (22106277,0), (1702909975,0), (1736464407,0), (299915791,0), (24562860103,0), (24831295559,0), (1384206501,0), (27810869,0), (362830351,0), (1290271,0), (1669421099,0), (1686198315,0), (24203429,0), (4311767095,0), (1702910007,0), (2004963413,0), (5455919,0), (524289039,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test4_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket3 4 h33Block4_0 = true := by decide +kernel
def h33Block4_1 : List NodeSpec := indexPairNodes [(29126525767,0), (29394961223,0), (1417760933,0), (306270293,0), (1300235279,0), (6078511,0), (8087117899,0), (8154226763,0), (376439567,0), (380634383,0), (19529130059,0), (128012453,0), (331436197,0), (368055175,0), (21944959879,0), (408962571,0), (18353213,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test4_1 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket3 4 h33Block4_1 = true := by decide +kernel
def h33Nodes4 : List NodeSpec := h33Block4_0 ++ h33Block4_1
lemma h33Check4 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket3 4 h33Nodes4 = true := by
  unfold h33Nodes4 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h33Test4_0,h33Test4_1⟩
def h33Bucket4 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes4
set_option maxRecDepth 200000 in
lemma h33Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 4 xs.toFinset) h33Bucket4 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33Bucket3Ok h33Check4
def h33Block5_0 : List NodeSpec := indexPairNodes [(221565,88), (541053,8), (573821,28), (672125,84), (704893,64), (2098282,1040), (811243,0), (241899,4), (2162778,528), (958699,0), (397437,335946), (35142781,73740), (135403,2052), (717131,849), (3469483,2560), (250091,22), (258283,6), (2179307,0), (2212075,0), (794869,10), (133183,1441), (629272683,256), (679604331,1889), (1057426507,64), (3797099,0), (36759659,0), (696381547,64), (713158763,0), (163704939,0), (813822059,1953), (44167275,0), (864153707,2017)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test5_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Block5_0 = true := by decide +kernel
def h33Block5_1 : List NodeSpec := indexPairNodes [(264344107,8), (52555883,0), (897708139,0), (880930923,8), (63969387,2), (729935979,1249), (746713195,0), (2982773,2), (3769205,2), (3048309,71789), (238423,118533), (58431,962723), (145471,0), (45094999,0), (946239,675), (2701193263,369), (1003583,2), (1028159,2), (2105407,675), (629182551,410691), (1015064607,836193), (1031841823,0), (2220095,6), (662736983,0), (981518367,0), (998295583,0), (2236479,6), (3137376343,52486213), (3170930775,205409), (3204485207,0), (3238039639,0), (612405335,52486213)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test5_1 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Block5_1 = true := by decide +kernel
def h33Block5_2 : List NodeSpec := indexPairNodes [(645959767,1441), (2264967199,0), (45132831,0), (2400319,0), (2734772271,0), (2197866527,0), (49327135,1569), (2433087,0), (2868989999,1697), (2465855,1569), (1556943,1090856045), (12453423,206889), (155715119,0), (914444405,1505), (65097775,1697), (2531391,1569), (146886703,1697), (2547775,1569), (2449612887,1569), (2315427927,369), (43035679,348321), (47229983,0), (750824479,0), (759213087,0), (767601695,7997985), (775990303,37929), (2351167,2404515), (612413527,345539), (12012642351,0), (9730940975,1000097), (2678847,6), (645967959,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test5_2 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Block5_2 = true := by decide +kernel
def h33Block5_3 : List NodeSpec := indexPairNodes [(11744239663,0), (9462538287,0), (2695231,6), (4076908631,3284501), (4110463063,172833), (4144017495,0), (4177571927,0), (595636311,3284501), (629190743,1441), (9865142319,63982853), (9596739631,0), (12683730991,0), (48484399,0), (2826303,0), (12415328303,0), (56873007,1761), (675310623,0), (2875455,0), (2239786015,1633), (2940991,1569), (3435551,1633), (2957375,1569), (830574709,1505), (47213599,1633), (2973759,1569), (6751631,5033567341), (13502751,62989), (181930271,0), (2583830615,1761), (2449645655,369), (44290095,356513), (52678703,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test5_3 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Block5_3 = true := by decide +kernel
def h33Block5_4 : List NodeSpec := indexPairNodes [(3573796911,0), (3607351343,0), (3640905775,19663457), (3674460207,12557), (2793535,708771), (641758239,369), (3088447,2), (3104831,2), (3121215,0), (3137599,0), (60302095,1633), (219167791,1633), (223347231,1633), (3170367,0), (236984407,2), (3186751,0), (987199,129137), (2842687,120945), (231746607,0), (3203135,0), (57937695,0), (3219519,0), (62399247,1569), (3235903,0), (245373015,2), (3252287,369), (2416703,0), (2859071,0), (2924607,1569), (2449471,1569), (985551,3553), (10880287,20865)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test5_4 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Block5_4 = true := by decide +kernel
def h33Block5_5 : List NodeSpec := indexPairNodes [(731599,3553), (207095343,1569), (11666991,2130465), (227391,1569), (239679,0), (35903,675), (774207,1569), (987535,3553), (953903,0), (2163999,0), (2166798,3553), (13766191,0), (3179284527,1569), (798783,1569), (778044959,1569), (206047519,1761), (10094879,2458337), (528447,1569), (147025967,0), (138612823,10785), (155390039,369), (62939223,10849), (159408215,369), (370148623,624994189), (137372431,25473), (58127,52823585), (3547919,9765409), (137279,0), (569407,675), (801118315,369), (809506923,2), (817891435,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test5_5 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Block5_5 = true := by decide +kernel
def h33Nodes5 : List NodeSpec := h33Block5_0 ++ h33Block5_1 ++ h33Block5_2 ++ h33Block5_3 ++ h33Block5_4 ++ h33Block5_5
lemma h33Check5 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket4 5 h33Nodes5 = true := by
  unfold h33Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h33Test5_0,h33Test5_1⟩,h33Test5_2⟩,h33Test5_3⟩,h33Test5_4⟩,h33Test5_5⟩
def h33Bucket5 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes5
set_option maxRecDepth 200000 in
lemma h33Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 5 xs.toFinset) h33Bucket5 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33Bucket4Ok h33Check5
def h33Block6_0 : List NodeSpec := indexPairNodes [(376,510), (378,3966), (23677,124), (1146,24124), (65658,167540), (63723,790108), (143595,1052222), (176363,2100854), (31871,252184590), (37951,248514606), (46143,400558182), (122,3710), (2917227,2414), (39899243,4852911), (11142763,4206), (10881643,200879), (41419883,209071), (38280299,32878), (66062443,786542), (1695851,80068751), (1712175,142880981), (1728559,88367173), (440351,71373333), (444447,176959701), (1342,26294373), (65854,22112357), (111039,8270037), (39999,641630475), (270783,27405), (42047,11079925903), (287167,119317), (48191,88608410663)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test6_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Block6_0 = true := by decide +kernel
def h33Block6_1 : List NodeSpec := indexPairNodes [(336319,26239045), (50239,2824701491), (352703,109609), (1876075,327386735), (318,6861655479), (23594047,2037869), (700479,2087338127), (708671,16667708455), (289437759,1368263), (306214975,188615), (1941611,5505485863), (897087,494929990), (281053247,475277), (297830463,1933579), (339773503,966797), (9307695,1444513557), (17039935,59661), (7736895,2041965), (219199,1769882225867), (272668735,2023623), (289445951,450759), (1351787,38799942), (299095,26243285), (149567,5130978927), (1908823,1174954053), (1101855,116412165), (1110047,981786693), (132163647,55409), (281061439,110755), (323004479,874609), (9831983,2048493333), (18088511,436997)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test6_1 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Block6_1 = true := by decide +kernel
def h33Block6_2 : List NodeSpec := indexPairNodes [(8261183,1905705), (888895,16662671), (1159199,131123981), (109599,5579885), (215103,244911294063), (127973439,8052935), (272676927,450759), (1368171,9610191), (307287,22060565), (153663,2824749199), (1925207,73503253), (5324847,206592533), (4767791,63982853), (123783231,135281), (132171839,270499), (281069631,710769), (5178175,174861), (5047615,355077), (8784159,78413852741), (905279,461375558), (5488687,429968141), (512047,5710957), (256063,161085186191), (119593023,5824711), (127981631,188615), (6144107,21746532495), (913471,11419791), (115402815,508713), (123791423,2065971), (132180031,1033001), (5440319,2041965), (5309759,986153)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test6_2 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Block6_2 = true := by decide +kernel
def h33Block6_3 : List NodeSpec := indexPairNodes [(9308447,91298754629), (716863,22988087), (31725119,874609), (31201855,710769), (30678591,481393), (120587327,692387), (979007,23360849207), (995391,46713947447), (692287,8275623), (32773695,110755), (32250431,270499), (31727167,110755), (124781631,2068643), (1011775,12217295047), (1019967,3188662471), (2891839,51016665647), (2908223,51008914743), (3055679,86805039), (2580543,22840951), (1036351,13559957111), (1044543,6914196791), (1642527,440510733), (264223,1386541), (260159,92276782), (198719,14365376655), (5702463,116419333), (17470,14042905), (66622,54817), (263214,29799269261), (755247,90973069), (206911,28725682375), (5964607,110049)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test6_3 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Block6_3 = true := by decide +kernel
def h33Block6_4 : List NodeSpec := indexPairNodes [(62527,2859207), (6095679,32225), (766015,60680342063), (1086,33261711), (544831,22955319), (6668395,4177889837), (20542,11593487385), (69694,31656473), (626223,8120919949), (52287,43401359), (790591,129935115895), (235583,22955319), (65598,528517190), (6570091,63820596825), (247071,34096910889), (44095,461375558), (446511,5380185), (223295,22840951), (6766639,1099016461), (247871,281353456679), (25955903,2198063877), (59679,72483245609), (182559,27995689), (243775,8331463), (25431615,120289), (26480191,64993), (231487,43401359), (33855,529270798), (536639,461375558), (3153983,7749775), (25359,3380717453), (202815,4701980051055)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test6_4 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Block6_4 = true := by decide +kernel
def h33Block6_5 : List NodeSpec := indexPairNodes [(70255679,73468432149), (274727999,69795), (35903,8331463), (99391,2068705), (7078975,32225)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test6_5 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Block6_5 = true := by decide +kernel
def h33Nodes6 : List NodeSpec := h33Block6_0 ++ h33Block6_1 ++ h33Block6_2 ++ h33Block6_3 ++ h33Block6_4 ++ h33Block6_5
lemma h33Check6 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket5 6 h33Nodes6 = true := by
  unfold h33Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h33Test6_0,h33Test6_1⟩,h33Test6_2⟩,h33Test6_3⟩,h33Test6_4⟩,h33Test6_5⟩
def h33Bucket6 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes6
set_option maxRecDepth 200000 in
lemma h33Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 6 xs.toFinset) h33Bucket6 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33Bucket5Ok h33Check6
def h33Block7_0 : List NodeSpec := indexPairNodes [(122,2158), (126,62327983), (585791,7737519), (389227,78), (190,752584303), (318,62010031), (12863,62327983), (157759,696256622), (161855,18819255335), (165951,9938175599), (170047,24171480687), (174143,7389087343), (178239,69815993967), (182335,19066029679), (186431,21750464655), (190527,44571592303), (602175,15582519), (618559,7790791), (634943,45845039), (643135,31164975), (651327,31164023), (659519,56329847), (574,27655965231), (1086,45554223), (2110,240945711), (4158,30877190703), (8254,615286391), (9791,31950931575), (32830,69263459959), (65598,494962790), (13887,73556967567), (14911,149256177263)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test7_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket6 7 h33Block7_0 = true := by decide +kernel
def h33Block7_1 : List NodeSpec := indexPairNodes [(15935,37852954767), (33855,260573262)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test7_1 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket6 7 h33Block7_1 = true := by decide +kernel
def h33Nodes7 : List NodeSpec := h33Block7_0 ++ h33Block7_1
lemma h33Check7 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket6 7 h33Nodes7 = true := by
  unfold h33Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h33Test7_0,h33Test7_1⟩
def h33Bucket7 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes7
set_option maxRecDepth 200000 in
lemma h33Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 7 xs.toFinset) h33Bucket7 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33Bucket6Ok h33Check7
def h33Block8_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Test8_0 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket7 8 h33Block8_0 = true := by decide +kernel
def h33Nodes8 : List NodeSpec := h33Block8_0
lemma h33Check8 : checkNodesBT h33W h33G h33Mask h33Pools h33Autos h33Bucket7 8 h33Nodes8 = true := h33Test8_0
def h33Bucket8 : BT (List (List Nat)) := buildBucketsBT h33W h33Nodes8
set_option maxRecDepth 200000 in
lemma h33Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h33G 8 xs.toFinset) h33Bucket8 := buildBucketsBT_sound (by decide) h33Pairs h33WOk h33PoolsOk h33AutosOk h33Bucket7Ok h33Check8
set_option maxRecDepth 200000 in
lemma h33Bound : Lower h33R h33G 9 := lower_of_forestBT (essPairs := [(VAR 0,0,1),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,1,17),(VAR 5,4,36)]) (by decide +kernel) h33Bucket8Ok (by decide +kernel)
namespace Cofactor12068
def R_0 : List Nat := varsOf 22
def G_0 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
lemma low_0 : Lower R_0 G_0 4 := carry_of (swaps := [(4,5),(1,2),(2,3)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound

def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(0,3),(0,4),(0,2),(0,1)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0

def G_2 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def R_2 : List Nat := varsOf 19
lemma low_2_ok : carryOK [(0,2),(0,1)] R_2 G_2 R_0 G_0 = true := by decide +kernel
lemma low_2 : Lower R_2 G_2 4 := carry_of low_2_ok low_0

def G_3 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def R_3 : List Nat := varsOf 21
lemma low_3_ok : carryOK [(0,1)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0

def G_7 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
def R_7 : List Nat := varsOf 23
def pos_7 : List Nat := [3,3,5,5,6,6,17,17,18,18,20,20,3,3,5,5,6,6,17,17,18,18,20,20]
def neg_7 : List Nat := [2,1,4,1,4,2,16,1,16,2,16,4,4,16,2,16,1,16,2,4,1,4,1,2]
def fmask_7 : Nat := fullMask 24
def base_7 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffff0000ffff0000ffff0000ffff0000,0xfc0fc0,0x2a540)]
def steps_7 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_7 : Array Decor := buildWires base_7 steps_7
def autos_7 : Array (List (Nat × Nat)) := #[[],[(2,4)],[(0,1)],[(2,4),(0,1)],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def slicesL_7 : List (Nat × Nat) := [(subcube 2 0,4),(subcube 1 0,4),(subcube 16 0,4),(subcube 4 0,4)]
def slices_7 : Array (Nat × Nat) := slicesL_7.toArray
def ps_7 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_7 : Array (Option BoundPool) := buildPools W_7 R_7 slices_7 ps_7
lemma gp_7 : goodPairs G_7 pos_7 neg_7 := goodPairs_of (by decide +kernel)
lemma base_7_ok : ∀ x ∈ base_7, faithful pos_7 neg_7 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma W_7_ok : ∀ x ∈ W_7.toList, faithful pos_7 neg_7 x ∧ x.1 < 2^128 := buildWires_faithful base_7_ok
lemma autos_7_ok : ∀ sw ∈ autos_7.toList, swapsValid sw = true ∧ permWord sw G_7 = G_7 := autos_of (by decide +kernel)
lemma sl_7_0_ok : sliceDirectCheck 2 0 0 R_7 G_7 R_3 G_3 = true := by decide +kernel
lemma sl_7_0 : Slice R_7 G_7 (subcube 2 0) 4 := slice_direct sl_7_0_ok low_3
lemma sl_7_1_ok : sliceDirectCheck 1 0 0 R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma sl_7_1 : Slice R_7 G_7 (subcube 1 0) 4 := slice_direct sl_7_1_ok low_0
lemma sl_7_2_ok : sliceDirectCheck 16 0 0 R_7 G_7 R_1 G_1 = true := by decide +kernel
lemma sl_7_2 : Slice R_7 G_7 (subcube 16 0) 4 := slice_direct sl_7_2_ok low_1
lemma sl_7_3_ok : sliceDirectCheck 4 0 0 R_7 G_7 R_2 G_2 = true := by decide +kernel
lemma sl_7_3 : Slice R_7 G_7 (subcube 4 0) 4 := slice_direct sl_7_3_ok low_2
set_option maxRecDepth 200000 in
lemma slices_7_ok : ∀ i (hi : i < slices_7.size), Slice R_7 G_7 slices_7[i].1 slices_7[i].2 :=
  array_forall_of_list (P := fun (p : Nat × Nat) => Slice R_7 G_7 p.1 p.2) (forall_cons sl_7_0 (forall_cons sl_7_1 (forall_cons sl_7_2 (forall_cons sl_7_3 (fun _ h => (List.not_mem_nil h).elim)))))
lemma P_7_ok : ∀ i (hi : i < P_7.size), ∀ c, P_7[i] = some c → ValidPool R_7 G_7 c := buildPools_sound slices_7_ok
def bk_7_init : Array (List (List Nat)) := #[]
lemma bk_7_init_ok : ∀ i (hi : i < bk_7_init.size), ∀ xs ∈ bk_7_init[i], Impossible G_7 (0 - 1) xs.toFinset := by intro i hi; simp [bk_7_init] at hi
def nodes_7_0 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_0 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_init 0 nodes_7_0 = true := by decide +kernel
def bk_7_0 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_0
lemma bk_7_0_ok : ∀ i (hi : i < bk_7_0.size), ∀ xs ∈ bk_7_0[i], Impossible G_7 0 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_init_ok chk_7_0
def nodes_7_1 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_1 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_0 1 nodes_7_1 = true := by decide +kernel
def bk_7_1 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_1
lemma bk_7_1_ok : ∀ i (hi : i < bk_7_1.size), ∀ xs ∈ bk_7_1[i], Impossible G_7 1 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_0_ok chk_7_1
def nodes_7_2 : List NodeSpec := []
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_2 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_1 2 nodes_7_2 = true := by decide +kernel
def bk_7_2 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_2
lemma bk_7_2_ok : ∀ i (hi : i < bk_7_2.size), ∀ xs ∈ bk_7_2[i], Impossible G_7 2 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_1_ok chk_7_2
def nodes_7_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_3 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_2 3 nodes_7_3 = true := by decide +kernel
def bk_7_3 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_3
lemma bk_7_3_ok : ∀ i (hi : i < bk_7_3.size), ∀ xs ∈ bk_7_3[i], Impossible G_7 3 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_2_ok chk_7_3
def nodes_7_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_4 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_3 4 nodes_7_4 = true := by decide +kernel
def bk_7_4 : Array (List (List Nat)) := buildBuckets 2 W_7 nodes_7_4
lemma bk_7_4_ok : ∀ i (hi : i < bk_7_4.size), ∀ xs ∈ bk_7_4[i], Impossible G_7 4 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_3_ok chk_7_4
def nodes_7_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_5 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_4 5 nodes_7_5 = true := by decide +kernel
def bk_7_5 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_5
lemma bk_7_5_ok : ∀ i (hi : i < bk_7_5.size), ∀ xs ∈ bk_7_5[i], Impossible G_7 5 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_4_ok chk_7_5
def nodes_7_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma chk_7_6 : checkNodes W_7 G_7 fmask_7 P_7 autos_7 bk_7_5 6 nodes_7_6 = true := by decide +kernel
def bk_7_6 : Array (List (List Nat)) := buildBuckets 1 W_7 nodes_7_6
lemma bk_7_6_ok : ∀ i (hi : i < bk_7_6.size), ∀ xs ∈ bk_7_6[i], Impossible G_7 6 xs.toFinset :=
  buildBuckets_sound (by decide) gp_7 W_7_ok P_7_ok autos_7_ok bk_7_5_ok chk_7_6
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_7_ok : forestRootCheck R_7 G_7 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma root_7_in : bucketContains bk_7_6 R_7 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 7 := lower_of_forest root_7_ok bk_7_6_ok root_7_in

end Cofactor12068
def h49R : List Nat := varsOf 53
def h49G : Nat := 0xfffffafafafaa0a0fffffafafafaa0a0
lemma h49Bound : Lower h49R h49G 7 := carry_of (swaps := [(4,5),(2,3),(3,4),(1,2)]) (roots2 := Cofactor12068.R_7) (T2 := Cofactor12068.G_7) (by decide +kernel) Cofactor12068.low_7
def h50R : List Nat := varsOf 60
def h50G : Nat := 0xfffffff0fff0f000fffffff0fff0f000
lemma h50Bound : Lower h50R h50G 7 := carry_of (swaps := [(2,3),(0,1),(1,2)]) (roots2 := h49R) (T2 := h49G) (by decide +kernel) h49Bound
def h51R : List Nat := varsOf 21
def h51G : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
lemma h51Bound : Lower h51R h51G 4 := carry_of (swaps := [(4,5),(1,2),(2,3),(0,1)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h52R : List Nat := varsOf 29
def h52G : Nat := 0xfafaa0aafafaa0aafafaa0aafafaa0aa
lemma h52Bound : Lower h52R h52G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,1,9)]) (by decide +kernel) h51Bound
def h53R : List Nat := varsOf 45
def h53G : Nat := 0xaafaaafaa0aaa0aaaafaaafaa0aaa0aa
lemma h53Bound : Lower h53R h53G 6 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1)]) (roots2 := h35R) (T2 := h35G) (by decide +kernel) h35Bound
def h54R : List Nat := varsOf 52
def h54G : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
lemma h54Bound : Lower h54R h54G 4 := carry_of (swaps := [(3,4)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h55R : List Nat := varsOf 53
def h55G : Nat := 0xfffffafafafaaaaafffffafafafaaaaa
lemma h55Bound : Lower h55R h55G 5 := carry_of (swaps := [(3,4)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h56R : List Nat := varsOf 57
def h56G : Nat := 0xaaffaaaaaaaa00aaaaffaaaaaaaa00aa
lemma h56Bound : Lower h56R h56G 6 := carry_of (swaps := [(3,4),(1,2),(0,1)]) (roots2 := h35R) (T2 := h35G) (by decide +kernel) h35Bound
def h57R : List Nat := varsOf 28
def h57G : Nat := 0xf0ff00f0f0ff00f0f0ff00f0f0ff00f0
lemma h57Bound : Lower h57R h57G 4 := carry_of (swaps := [(4,5),(3,4),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h58R : List Nat := varsOf 60
def h58G : Nat := 0xf0ff00f0f0f00000f0ff00f0f0f00000
lemma h58Bound : Lower h58R h58G 5 := carry_of (swaps := [(3,4)]) (roots2 := h44R) (T2 := h44G) (by decide +kernel) h44Bound
def h59R : List Nat := varsOf 29
def h59G : Nat := 0xfaffaafafaffaafafaffaafafaffaafa
lemma h59Bound : Lower h59R h59G 5 := carry_of (swaps := [(3,4)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h60R : List Nat := varsOf 53
def h60G : Nat := 0xfafaaaaafafaa0a0fafaaaaafafaa0a0
lemma h60Bound : Lower h60R h60G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(0,1),(1,2)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h48R : List Nat := varsOf 61
def h48G : Nat := 0xfaffaafafafaa0aafaffaafafafaa0aa
def h48Pos : List Nat := [1,20,5,13,1,36,1,13,20,25,36,41,48,25,48,57,45,1,36,17,28,20,48,28,5,28,60,60,41,17,33,41,1,52,48,52,17,1,5,41,52,33,45,28,28,28,28]
def h48Neg : List Nat := [0,16,4,9,4,44,9,12,4,9,4,9,56,24,16,56,44,16,32,16,9,0,32,12,0,24,44,56,44,9,32,32,32,32,0,4,0,8,9,40,16,0,9,16,8,44,56]
def h48Mask : Nat := fullMask 47
def h48Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x6f1f10baadd,0x44020100a48),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7d4a0fb505ae,0x2008148105b4),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x7c809e91aa88,0x74e03e91bae8),(0xffff0000ffff0000ffff0000ffff0000,0x791e2ef8f302,0x49000a0af002),(0xffffffff00000000ffffffff00000000,0x78edc45dc20,0x6083dc459020)]
def h48Steps : List (Nat × Nat × Nat) := [(1,0,1),(2,0,1),(0,0,2),(1,0,2),(1,0,3),(1,1,2),(3,1,2),(0,1,3),(1,1,3),(2,2,4),(3,2,4),(1,2,5),(3,2,5),(0,2,13),(1,2,13),(2,2,13),(3,2,13),(0,4,5),(2,4,5),(0,4,13),(1,4,13),(2,4,13),(3,4,13),(0,5,9),(1,5,9),(2,5,13),(3,1,3),(1,1,4),(3,1,4),(3,1,9),(1,2,3),(2,2,3),(1,3,4),(3,3,4),(3,3,5),(3,3,9),(1,3,34),(0,0,4),(1,0,4),(2,0,4),(3,0,4),(0,0,13),(3,0,13),(0,2,29),(3,2,29),(0,4,29),(3,4,29),(1,1,40),(2,5,40),(2,2,46),(1,4,46),(2,4,46),(3,1,35),(3,0,57),(1,3,57),(0,5,35),(1,0,15),(1,1,61),(3,1,61),(1,1,15),(3,0,64),(1,3,64),(3,3,64),(1,3,15),(3,3,62),(2,5,15),(3,0,16),(1,3,71),(1,1,38),(1,0,73),(3,3,73),(2,5,38),(1,1,22),(1,0,23),(3,1,78),(3,3,78),(1,1,7),(1,3,81),(3,3,81),(3,7,13),(0,3,77),(1,3,77),(2,3,77),(3,3,77),(2,13,42),(3,3,43),(0,13,43),(3,13,43),(1,3,92),(1,3,33),(3,0,94),(3,1,94),(1,1,44),(1,3,97),(3,3,97),(2,13,44),(1,1,36),(3,3,10),(1,0,102),(3,11,37),(2,29,46),(2,13,15),(1,4,18),(0,4,19),(3,18,19),(3,24,25),(1,2,26),(2,2,27)]
def h48W : BT Decor := buildWiresBT 7 h48Base h48Steps
def h48AutoList : List (List (Nat × Nat)) := [[],[(2,4)]]
def h48Autos : BT (List (Nat × Nat)) := btOfList 1 h48AutoList
lemma h48Pairs : goodPairs h48G h48Pos h48Neg := goodPairs_of (by decide +kernel)
lemma h48BaseOk : ∀ x ∈ h48Base, faithful h48Pos h48Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h48WOk : btAll (fun x => faithful h48Pos h48Neg x ∧ x.1 < 2^128) h48W := buildWiresBT_faithful h48BaseOk
lemma h48AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h48G = h48G) h48Autos := btAll_ofList (autos_of (by decide +kernel))
def h48SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 4 0,6),some (subcubeFast 8 0,5),some (subcubeFast 9 0,4),some (subcubeFast 16 0,6),some (subcubeFast 32 0,5),some (subcubeFast 32 8,4),some (0xaa55aa55aa55aa55aa55aa55aa55aa55,7),some (0xff00ffff00ff0000ff00ffff00ff00,7)]
def h48Slices : BT (Option (Nat × Nat)) := btOfList 4 h48SliceList
def h48Specs : List PoolSpec := poolSteps h48Steps [(4,[]),(2,[]),(6,[]),(10,[0]),(7,[0]),(4,[4]),(5,[0,4]),(1,[0,4]),(7,[]),(3,[]),(10,[]),(0,[]),(8,[]),(1,[]),(5,[0]),(1,[0]),(10,[30]),(10,[10]),(10,[0,12]),(9,[]),(7,[0,44]),(7,[0,45]),(4,[34]),(5,[]),(10,[1]),(7,[1]),(7,[29]),(4,[2]),(7,[2]),(10,[76]),(4,[3]),(7,[3]),(4,[37]),(10,[37]),(7,[37]),(10,[8]),(11,[8]),(4,[17,81]),(4,[37,84]),(4,[17]),(11,[]),(4,[38]),(10,[38]),(7,[38]),(4,[38,86]),(4,[38,87]),(5,[38]),(0,[28]),(4,[39]),(10,[39]),(7,[39]),(4,[40]),(10,[40]),(7,[40]),(10,[5]),(7,[5]),(10,[0,66]),(4,[31]),(8,[31]),(8,[5]),(10,[5,97]),(4,[97]),(10,[6]),(7,[6]),(4,[10]),(8,[6]),(2,[10]),(4,[30]),(7,[52]),(4,[41]),(4,[41,49]),(4,[41,50]),(4,[41,51]),(4,[4,44]),(4,[4,45]),(4,[4,46]),(4,[25]),(4,[42]),(7,[42]),(4,[9]),(11,[8,101]),(4,[13]),(11,[8,13]),(4,[13,102]),(4,[14]),(4,[14,103]),(4,[15]),(4,[15,16]),(4,[16]),(4,[19]),(4,[19,20]),(4,[20]),(4,[21]),(7,[68]),(4,[21,106]),(11,[8,22]),(4,[22]),(4,[22,107]),(10,[27]),(7,[27]),(10,[10,27]),(0,[27]),(4,[33]),(0,[33]),(10,[28]),(7,[28]),(4,[89]),(10,[9]),(7,[9]),(7,[10]),(10,[10,56]),(5,[56])]
def h48Pools : BT (Option BoundPool) := buildPoolsBT 7 h48W h48R h48Slices h48Specs
set_option maxRecDepth 200000 in
lemma h48Slice11 : Slice h48R h48G (0xff00ffff00ff0000ff00ffff00ff00) 7 := opposite_slice (oppositeRow 3 5 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
lemma h48Slice10 : Slice h48R h48G (0xaa55aa55aa55aa55aa55aa55aa55aa55) 7 := mapped_slice (identifyRow 0 3 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
lemma h48Slice9 : Slice h48R h48G (subcubeFast 32 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
lemma h48Slice8 : Slice h48R h48G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h52Bound
set_option maxRecDepth 200000 in
lemma h48Slice7 : Slice h48R h48G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h53Bound
set_option maxRecDepth 200000 in
lemma h48Slice6 : Slice h48R h48G (subcubeFast 9 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
lemma h48Slice5 : Slice h48R h48G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h55Bound
set_option maxRecDepth 200000 in
lemma h48Slice4 : Slice h48R h48G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h56Bound
set_option maxRecDepth 200000 in
lemma h48Slice3 : Slice h48R h48G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h57Bound
set_option maxRecDepth 200000 in
lemma h48Slice2 : Slice h48R h48G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h58Bound
set_option maxRecDepth 200000 in
lemma h48Slice1 : Slice h48R h48G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h59Bound
set_option maxRecDepth 200000 in
lemma h48Slice0 : Slice h48R h48G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h60Bound
lemma h48SlicesOk : btAll (sliceSpec h48R h48G) h48Slices := btAll_ofList (P := sliceSpec h48R h48G) (sliceSpecCons h48Slice0 (sliceSpecCons h48Slice1 (sliceSpecCons h48Slice2 (sliceSpecCons h48Slice3 (sliceSpecCons h48Slice4 (sliceSpecCons h48Slice5 (sliceSpecCons h48Slice6 (sliceSpecCons h48Slice7 (sliceSpecCons h48Slice8 (sliceSpecCons h48Slice9 (sliceSpecCons h48Slice10 (sliceSpecCons h48Slice11 sliceSpecNil))))))))))))
set_option maxRecDepth 200000 in
lemma h48PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h48R h48G c) h48Pools := buildPoolsBT_sound h48SlicesOk
def h48Empty : BT (List (List Nat)) := BT.empty
lemma h48EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G (3 - 1) xs.toFinset) h48Empty := trivial
def h48Block3_0 : List NodeSpec := nodesWithIdentity [([2,4,28,92],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test3_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Empty 3 h48Block3_0 = true := by decide +kernel
def h48Nodes3 : List NodeSpec := h48Block3_0
lemma h48Check3 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Empty 3 h48Nodes3 = true := h48Test3_0
def h48Bucket3 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes3
set_option maxRecDepth 200000 in
lemma h48Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 3 xs.toFinset) h48Bucket3 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48EmptyOk h48Check3
def h48Block4_0 : List NodeSpec := indexPairNodes [(1073199,0), (8156219,0), (17333291,0), (1366039,0), (1890327,0), (1370135,0), (6864971,4929), (108020797,0), (337643595,5953), (1367359771,0), (377701191,0), (1663093,0), (1728599,0), (440351,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test4_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket3 4 h48Block4_0 = true := by decide +kernel
def h48Nodes4 : List NodeSpec := h48Block4_0
lemma h48Check4 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket3 4 h48Nodes4 = true := h48Test4_0
def h48Bucket4 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes4
set_option maxRecDepth 200000 in
lemma h48Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 4 xs.toFinset) h48Bucket4 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket3Ok h48Check4
def h48Block5_0 : List NodeSpec := indexTripleNodes [(17512,998,2), (3342973,4,2), (17514,518,2), (241899,369,2), (52287,3953,2), (794869,0,2), (35128445,2,2), (36177021,2,2), (55578955,514,2), (860395,369,2), (2422831,369,2), (231487,512,2), (223295,369,2), (925941,1034,2), (975083,1905,2), (239679,6656,2), (544831,0,2), (2179317,369,2), (2244843,4,2), (806959,465,2), (577599,465,2), (593983,512,2), (178239,0,2), (38836341,369,2), (62527,0,2), (2922603,369,2), (40933463,401,2), (43030615,39025,6), (11282975,13521,6), (11807263,433,2), (696565,369,2), (729303,1377,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test5_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Block5_0 = true := by decide +kernel
def h48Block5_1 : List NodeSpec := indexTripleNodes [(745567,1441,6), (2408693,369,2), (143658091,512,2), (643135,6769,2), (659519,0,2), (651327,0,2), (135269483,74240,2), (675903,209073,2), (700479,499747,2), (142762091,86099221,2), (159539307,3761,2), (176316523,0,2), (193093739,0,2), (195082347,4,2), (692287,4,2), (716863,44549,2), (725055,5953,2), (216024095,1313,2), (60307999,0,2), (141558891,465,2), (203470955,465,2), (733247,465,2), (177212523,512,2), (774207,344721,2), (790591,0,2), (782399,0,2), (561215,0,2), (815167,0,2), (188776983,1569,2), (46668887,465,2), (15076951,2,2), (44830315,401,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test5_1 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Block5_1 = true := by decide +kernel
def h48Block5_2 : List NodeSpec := indexTripleNodes [(188756015,1569,2), (823359,0,2), (36739189,0,2), (43519063,18305,2), (11142431,18561,2), (11404575,18817,2), (11275371,675,2), (38276183,19073,2), (9831711,19329,2), (10093855,19585,2), (36743285,0,2), (41421931,675,2), (54004843,512,2), (256063,0,2), (839743,120604817,2), (62551,4161825,2), (49546527,21633,2), (46664811,1917091,2), (50070815,22145,2), (185601131,675,2), (198743,22657,2), (54815,23425,2), (175115371,675,2), (63442027,5472419,2), (206572631,24449,2), (56863,10027297,2), (208669783,25217,2), (38286879,2,2), (15862047,1569,6), (626751,0,2), (749631,0,2), (243775,0,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test5_2 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Block5_2 = true := by decide +kernel
def h48Block5_3 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,65],[]),([0,1,2,3,4,67],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test5_3 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Block5_3 = true := by decide +kernel
def h48Nodes5 : List NodeSpec := h48Block5_0 ++ h48Block5_1 ++ h48Block5_2 ++ h48Block5_3
lemma h48Check5 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket4 5 h48Nodes5 = true := by
  unfold h48Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h48Test5_0,h48Test5_1⟩,h48Test5_2⟩,h48Test5_3⟩
def h48Bucket5 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes5
set_option maxRecDepth 200000 in
lemma h48Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 5 xs.toFinset) h48Bucket5 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket4Ok h48Check5
def h48Block6_0 : List NodeSpec := indexTripleNodes [(1148,1646,6), (1150,614,6), (581877,1582,2), (16506,98854,2), (125055,135690,2), (65662,291866,2), (23679,6168,2), (25727,530458,2), (274559,26114,2), (52287,3953,6), (100479,1584,6), (145471,25195046,6), (282751,550,6), (71807,25606,2), (75903,7761,2), (153663,151025230,2), (16702,9586407,6), (634943,680143847,2), (16958,15876493,2), (7734847,253502695,6), (1204331,3605781,2), (602175,554114383,2), (7996991,23437745,2), (2767391,3637552583,2), (618559,2766311,6), (8259135,37233895,6), (766015,3423874383,2), (17040959,10096209,2), (553023,182512267,6), (3476055,63334587019,2), (806975,1855695527655,6), (69686,62680998667,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test6_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Block6_0 = true := by decide +kernel
def h48Block6_1 : List NodeSpec := indexTripleNodes [(1738559,2767907,2), (227391,14563294543,2), (17565247,289501415,6), (4326975,499781,6), (4589119,154629,6), (178239,807433251,2), (18089535,2277607,6), (49214,373754581905,2), (81982,244998356003,6), (540734,12216715409,2), (427583,13022021777,6), (493119,133187729,6), (4210750,274745489,2), (1508927,5013937,2), (1639999,5145009,6), (1771071,948036017,6), (1902143,1015144881,2), (2296095,0x628126051c63,6), (865823,7831829027,2), (585791,2613085615591,6), (610367,32262,6), (741439,226023874279,6), (235583,116512792399,6), (247871,1392742119,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test6_1 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Block6_1 = true := by decide +kernel
def h48Nodes6 : List NodeSpec := h48Block6_0 ++ h48Block6_1
lemma h48Check6 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket5 6 h48Nodes6 = true := by
  unfold h48Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h48Test6_0,h48Test6_1⟩
def h48Bucket6 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes6
set_option maxRecDepth 200000 in
lemma h48Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 6 xs.toFinset) h48Bucket6 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket5Ok h48Check6
def h48Block7_0 : List NodeSpec := indexTripleNodes [(126,32318,2), (190,30693199,6), (318,822111750,6), (574,6460309006,2), (157759,113382270287,6), (161855,4119150415,6), (165951,32617571663,6), (170047,7533313871,2), (2110,136374971019,6), (4158,444538856783,6), (9791,478486247,6), (58431,437015360999,6), (60479,224950195687,6), (32830,0xf20780604a754f,2), (65598,0x2d822030a33e8b,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test7_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket6 7 h48Block7_0 = true := by decide +kernel
def h48Nodes7 : List NodeSpec := h48Block7_0
lemma h48Check7 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket6 7 h48Nodes7 = true := h48Test7_0
def h48Bucket7 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes7
set_option maxRecDepth 200000 in
lemma h48Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 7 xs.toFinset) h48Bucket7 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket6Ok h48Check7
def h48Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,8,10,40],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Test8_0 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket7 8 h48Block8_0 = true := by decide +kernel
def h48Nodes8 : List NodeSpec := h48Block8_0
lemma h48Check8 : checkNodesBT h48W h48G h48Mask h48Pools h48Autos h48Bucket7 8 h48Nodes8 = true := h48Test8_0
def h48Bucket8 : BT (List (List Nat)) := buildBucketsBT h48W h48Nodes8
set_option maxRecDepth 200000 in
lemma h48Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h48G 8 xs.toFinset) h48Bucket8 := buildBucketsBT_sound (by decide) h48Pairs h48WOk h48PoolsOk h48AutosOk h48Bucket7Ok h48Check8
set_option maxRecDepth 200000 in
lemma h48Bound : Lower h48R h48G 9 := lower_of_forestBT (essPairs := [(VAR 0,0,1),(VAR 2,9,13),(VAR 3,1,9),(VAR 4,4,20),(VAR 5,4,36)]) (by decide +kernel) h48Bucket8Ok (by decide +kernel)
def h62R : List Nat := varsOf 53
def h62G : Nat := 0xafafaaaafafaaaaaafafaaaafafaaaaa
lemma h62Bound : Lower h62R h62G 5 := lift_of (z := 1) (o := 16) (essPairs := [(VAR 0,0,1),(VAR 4,4,20)]) (by decide +kernel) h6Bound
def h63R : List Nat := varsOf 57
def h63G : Nat := 0xffffffaaff00aa00ffffffaaff00aa00
lemma h63Bound : Lower h63R h63G 5 := carry_of (swaps := [(2,3),(3,4),(2,3)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h64R : List Nat := varsOf 53
def h64G : Nat := 0xffffafaf0a0a0a0affffafaf0a0a0a0a
lemma h64Bound : Lower h64R h64G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(2,3),(0,1)]) (roots2 := h9R) (T2 := h9G) (by decide +kernel) h9Bound
def h65R : List Nat := varsOf 57
def h65G : Nat := 0xffaaffaaff00aaaaffaaffaaff00aaaa
lemma h65Bound : Lower h65R h65G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(1,2),(2,3),(0,1)]) (roots2 := h12R) (T2 := h12G) (by decide +kernel) h12Bound
def h66R : List Nat := varsOf 60
def h66G : Nat := 0xfffffff0f000f000fffffff0f000f000
lemma h66Bound : Lower h66R h66G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h67R : List Nat := varsOf 29
def h67G : Nat := 0xfa0aaa0afa0aaa0afa0aaa0afa0aaa0a
lemma h67Bound : Lower h67R h67G 4 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,12,28)]) (by decide +kernel) h4Bound
def h68R : List Nat := varsOf 45
def h68G : Nat := 0xafaaafaaaa0aaa0aafaaafaaaa0aaa0a
lemma h68Bound : Lower h68R h68G 6 := carry_of (swaps := [(1,2),(2,3),(3,4),(2,3),(0,1)]) (roots2 := h35R) (T2 := h35G) (by decide +kernel) h35Bound
def h69R : List Nat := varsOf 37
def h69G : Nat := 0xafafafaf0a0a0a0aafafafaf0a0a0a0a
lemma h69Bound : Lower h69R h69G 4 := carry_of (swaps := [(3,4),(4,5),(3,4),(2,3),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h70R : List Nat := varsOf 53
def h70G : Nat := 0xafafaaaa0a0a0a0aafafaaaa0a0a0a0a
lemma h70Bound : Lower h70R h70G 5 := carry_of (swaps := [(2,3),(3,4),(2,3)]) (roots2 := h41R) (T2 := h41G) (by decide +kernel) h41Bound
def h71R : List Nat := varsOf 28
def h71G : Nat := 0xff0f0f00ff0f0f00ff0f0f00ff0f0f00
lemma h71Bound : Lower h71R h71G 4 := carry_of (swaps := [(4,5),(3,4),(1,2),(2,3)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h72R : List Nat := varsOf 44
def h72G : Nat := 0xff0fff0ff000f000ff0fff0ff000f000
lemma h72Bound : Lower h72R h72G 3 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(2,3),(1,2)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h73R : List Nat := varsOf 52
def h73G : Nat := 0xffff0f0ff0f00000ffff0f0ff0f00000
lemma h73Bound : Lower h73R h73G 3 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(2,3),(3,4),(1,2)]) (roots2 := h4R) (T2 := h4G) (by decide +kernel) h4Bound
def h74R : List Nat := varsOf 60
def h74G : Nat := 0xff0f0f00f0000000ff0f0f00f0000000
def h74Pos : List Nat := [40,48,40,48,28,40,28,40,48,28,28,56]
def h74Neg : List Nat := [32,52,36,32,12,8,20,44,16,16,24,24]
def h74Mask : Nat := fullMask 12
def h74Base : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1616,214),(0xff00ff00ff00ff00ff00ff00ff00ff00,3829,3248),(0xffff0000ffff0000ffff0000ffff0000,3930,3906),(0xffffffff00000000ffffffff00000000,2479,143)]
def h74Steps : List (Nat × Nat × Nat) := [(0,0,1),(3,0,1),(3,0,3),(0,1,2),(2,2,5)]
def h74W : BT Decor := buildWiresBT 4 h74Base h74Steps
def h74AutoList : List (List (Nat × Nat)) := [[],[(3,4)]]
def h74Autos : BT (List (Nat × Nat)) := btOfList 1 h74AutoList
lemma h74Pairs : goodPairs h74G h74Pos h74Neg := goodPairs_of (by decide +kernel)
lemma h74BaseOk : ∀ x ∈ h74Base, faithful h74Pos h74Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h74WOk : btAll (fun x => faithful h74Pos h74Neg x ∧ x.1 < 2^128) h74W := buildWiresBT_faithful h74BaseOk
lemma h74AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h74G = h74G) h74Autos := btAll_ofList (autos_of (by decide +kernel))
def h74SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,3),some (subcubeFast 0 16,3),some (subcubeFast 0 32,4),some (0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0,4)]
def h74Slices : BT (Option (Nat × Nat)) := btOfList 2 h74SliceList
def h74Specs : List PoolSpec := [(2,[]),(3,[]),(0,[]),(1,[])]
def h74Pools : BT (Option BoundPool) := buildPoolsBT 2 h74W h74R h74Slices h74Specs
set_option maxRecDepth 200000 in
lemma h74Slice3 : Slice h74R h74G (0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0) 4 := opposite_slice (oppositeRow 2 5 56) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
lemma h74Slice2 : Slice h74R h74G (subcubeFast 0 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h71Bound
set_option maxRecDepth 200000 in
lemma h74Slice1 : Slice h74R h74G (subcubeFast 0 16) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h72Bound
set_option maxRecDepth 200000 in
lemma h74Slice0 : Slice h74R h74G (subcubeFast 0 8) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h73Bound
lemma h74SlicesOk : btAll (sliceSpec h74R h74G) h74Slices := btAll_ofList (P := sliceSpec h74R h74G) (sliceSpecCons h74Slice0 (sliceSpecCons h74Slice1 (sliceSpecCons h74Slice2 (sliceSpecCons h74Slice3 sliceSpecNil))))
lemma h74PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h74R h74G c) h74Pools := buildPoolsBT_sound h74SlicesOk
def h74Empty : BT (List (List Nat)) := BT.empty
lemma h74EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h74G (2 - 1) xs.toFinset) h74Empty := trivial
def h74Block2_0 : List NodeSpec := nodesWithIdentity [([1,6,8],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h74Test2_0 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Empty 2 h74Block2_0 = true := by decide +kernel
def h74Nodes2 : List NodeSpec := h74Block2_0
lemma h74Check2 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Empty 2 h74Nodes2 = true := h74Test2_0
def h74Bucket2 : BT (List (List Nat)) := buildBucketsBT h74W h74Nodes2
lemma h74Bucket2Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h74G 2 xs.toFinset) h74Bucket2 := buildBucketsBT_sound (by decide) h74Pairs h74WOk h74PoolsOk h74AutosOk h74EmptyOk h74Check2
def h74Block3_0 : List NodeSpec := indexPairNodes [(172,0), (204,0), (534,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h74Test3_0 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Bucket2 3 h74Block3_0 = true := by decide +kernel
def h74Nodes3 : List NodeSpec := h74Block3_0
lemma h74Check3 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Bucket2 3 h74Nodes3 = true := h74Test3_0
def h74Bucket3 : BT (List (List Nat)) := buildBucketsBT h74W h74Nodes3
lemma h74Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h74G 3 xs.toFinset) h74Bucket3 := buildBucketsBT_sound (by decide) h74Pairs h74WOk h74PoolsOk h74AutosOk h74Bucket2Ok h74Check3
def h74Block4_0 : List NodeSpec := indexTripleNodes [(62,6,2), (94,16,2), (142,2,6), (286,8,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h74Test4_0 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Bucket3 4 h74Block4_0 = true := by decide +kernel
def h74Nodes4 : List NodeSpec := h74Block4_0
lemma h74Check4 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Bucket3 4 h74Nodes4 = true := h74Test4_0
def h74Bucket4 : BT (List (List Nat)) := buildBucketsBT h74W h74Nodes4
lemma h74Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h74G 4 xs.toFinset) h74Bucket4 := buildBucketsBT_sound (by decide) h74Pairs h74WOk h74PoolsOk h74AutosOk h74Bucket3Ok h74Check4
def h74Block5_0 : List NodeSpec := [([0,1,2,3],[0,2,3],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h74Test5_0 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Bucket4 5 h74Block5_0 = true := by decide +kernel
def h74Nodes5 : List NodeSpec := h74Block5_0
lemma h74Check5 : checkNodesBT h74W h74G h74Mask h74Pools h74Autos h74Bucket4 5 h74Nodes5 = true := h74Test5_0
def h74Bucket5 : BT (List (List Nat)) := buildBucketsBT h74W h74Nodes5
lemma h74Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h74G 5 xs.toFinset) h74Bucket5 := buildBucketsBT_sound (by decide) h74Pairs h74WOk h74PoolsOk h74AutosOk h74Bucket4Ok h74Check5
lemma h74Bound : Lower h74R h74G 6 := lower_of_forestBT (essPairs := [(VAR 2,24,28),(VAR 3,20,28),(VAR 4,12,28),(VAR 5,8,40)]) (by decide +kernel) h74Bucket5Ok (by decide +kernel)
def h75R : List Nat := varsOf 29
def h75G : Nat := 0xffafafaaffafafaaffafafaaffafafaa
lemma h75Bound : Lower h75R h75G 5 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h76R : List Nat := varsOf 45
def h76G : Nat := 0xffafffaffa0afa0affafffaffa0afa0a
def h76Pos : List Nat := [1,12,1,37,1,13,12,32,37,32,40,13,9,44]
def h76Neg : List Nat := [0,8,5,36,4,5,4,0,5,36,8,8,8,36]
def h76Mask : Nat := fullMask 14
def h76Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,6461,292),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x296a,9084),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3c62,7170),(0xffffffff00000000ffffffff00000000,0x2788,8712)]
def h76Steps : List (Nat × Nat × Nat) := [(1,0,1),(3,0,1),(1,0,3),(2,1,2),(1,3,5)]
def h76W : BT Decor := buildWiresBT 4 h76Base h76Steps
def h76AutoList : List (List (Nat × Nat)) := [[],[(0,5)]]
def h76Autos : BT (List (Nat × Nat)) := btOfList 1 h76AutoList
lemma h76Pairs : goodPairs h76G h76Pos h76Neg := goodPairs_of (by decide +kernel)
lemma h76BaseOk : ∀ x ∈ h76Base, faithful h76Pos h76Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h76WOk : btAll (fun x => faithful h76Pos h76Neg x ∧ x.1 < 2^128) h76W := buildWiresBT_faithful h76BaseOk
lemma h76AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h76G = h76G) h76Autos := btAll_ofList (autos_of (by decide +kernel))
def h76SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 1 0,3),some (subcubeFast 8 0,4),some (subcubeFast 32 0,3),some (0xff00ff00ff00ff00ff00ff00ff00ff0,4)]
def h76Slices : BT (Option (Nat × Nat)) := btOfList 2 h76SliceList
def h76Specs : List PoolSpec := [(0,[]),(1,[]),(3,[]),(2,[])]
def h76Pools : BT (Option BoundPool) := buildPoolsBT 2 h76W h76R h76Slices h76Specs
set_option maxRecDepth 200000 in
lemma h76Slice3 : Slice h76R h76G (0xff00ff00ff00ff00ff00ff00ff00ff0) 4 := opposite_slice (oppositeRow 2 3 41) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
lemma h76Slice2 : Slice h76R h76G (subcubeFast 32 0) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
lemma h76Slice1 : Slice h76R h76G (subcubeFast 8 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h69Bound
set_option maxRecDepth 200000 in
lemma h76Slice0 : Slice h76R h76G (subcubeFast 1 0) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h72Bound
lemma h76SlicesOk : btAll (sliceSpec h76R h76G) h76Slices := btAll_ofList (P := sliceSpec h76R h76G) (sliceSpecCons h76Slice0 (sliceSpecCons h76Slice1 (sliceSpecCons h76Slice2 (sliceSpecCons h76Slice3 sliceSpecNil))))
lemma h76PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h76R h76G c) h76Pools := buildPoolsBT_sound h76SlicesOk
def h76Empty : BT (List (List Nat)) := BT.empty
lemma h76EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h76G (2 - 1) xs.toFinset) h76Empty := trivial
def h76Block2_0 : List NodeSpec := nodesWithIdentity [([0,7,8],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h76Test2_0 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Empty 2 h76Block2_0 = true := by decide +kernel
def h76Nodes2 : List NodeSpec := h76Block2_0
lemma h76Check2 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Empty 2 h76Nodes2 = true := h76Test2_0
def h76Bucket2 : BT (List (List Nat)) := buildBucketsBT h76W h76Nodes2
lemma h76Bucket2Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h76G 2 xs.toFinset) h76Bucket2 := buildBucketsBT_sound (by decide) h76Pairs h76WOk h76PoolsOk h76AutosOk h76EmptyOk h76Check2
def h76Block3_0 : List NodeSpec := indexPairNodes [(306,0), (338,0), (526,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h76Test3_0 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Bucket2 3 h76Block3_0 = true := by decide +kernel
def h76Nodes3 : List NodeSpec := h76Block3_0
lemma h76Check3 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Bucket2 3 h76Nodes3 = true := h76Test3_0
def h76Bucket3 : BT (List (List Nat)) := buildBucketsBT h76W h76Nodes3
lemma h76Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h76G 3 xs.toFinset) h76Bucket3 := buildBucketsBT_sound (by decide) h76Pairs h76WOk h76PoolsOk h76AutosOk h76Bucket2Ok h76Check3
def h76Block4_0 : List NodeSpec := indexTripleNodes [(62,12,2), (94,16,2), (158,2,2), (278,4,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h76Test4_0 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Bucket3 4 h76Block4_0 = true := by decide +kernel
def h76Nodes4 : List NodeSpec := h76Block4_0
lemma h76Check4 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Bucket3 4 h76Nodes4 = true := h76Test4_0
def h76Bucket4 : BT (List (List Nat)) := buildBucketsBT h76W h76Nodes4
lemma h76Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h76G 4 xs.toFinset) h76Bucket4 := buildBucketsBT_sound (by decide) h76Pairs h76WOk h76PoolsOk h76AutosOk h76Bucket3Ok h76Check4
def h76Block5_0 : List NodeSpec := [([0,1,2,3],[0,1,3],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h76Test5_0 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Bucket4 5 h76Block5_0 = true := by decide +kernel
def h76Nodes5 : List NodeSpec := h76Block5_0
lemma h76Check5 : checkNodesBT h76W h76G h76Mask h76Pools h76Autos h76Bucket4 5 h76Nodes5 = true := h76Test5_0
def h76Bucket5 : BT (List (List Nat)) := buildBucketsBT h76W h76Nodes5
lemma h76Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h76G 5 xs.toFinset) h76Bucket5 := buildBucketsBT_sound (by decide) h76Pairs h76WOk h76PoolsOk h76AutosOk h76Bucket4Ok h76Check5
lemma h76Bound : Lower h76R h76G 6 := lower_of_forestBT (essPairs := [(VAR 0,0,1),(VAR 2,1,5),(VAR 3,4,12),(VAR 5,0,32)]) (by decide +kernel) h76Bucket5Ok (by decide +kernel)
def h77R : List Nat := varsOf 53
def h77G : Nat := 0xffffafaffafaaaaaffffafaffafaaaaa
lemma h77Bound : Lower h77R h77G 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(2,3)]) (roots2 := h31R) (T2 := h31G) (by decide +kernel) h31Bound
def h78R : List Nat := varsOf 57
def h78G : Nat := 0xffaaaaaaff00aa00ffaaaaaaff00aa00
lemma h78Bound : Lower h78R h78G 4 := carry_of (swaps := [(2,3),(3,4),(2,3)]) (roots2 := h46R) (T2 := h46G) (by decide +kernel) h46Bound
def h61R : List Nat := varsOf 61
def h61G : Nat := 0xffafafaafa0aaa0affafafaafa0aaa0a
def h61Pos : List Nat := [1,28,1,13,1,40,13,28,48,37,40,9,37,17,37,28,48,17,53,33,9,48,60,40,40,45,60,28,9,33,28,40,40,60,53,13,13,29,48,1,25,13,28,1,17,17,1,56,33,37,25,45,60,48,28,28,13]
def h61Neg : List Nat := [0,24,5,12,4,32,5,12,32,5,8,8,36,21,32,20,16,16,52,32,5,52,52,36,44,44,44,16,12,5,52,0,12,24,21,8,44,21,24,8,24,4,21,32,20,5,21,24,0,4,21,5,20,36,8,4,21]
def h61Mask : Nat := fullMask 57
def h61Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x10f7bbc321e7a5d,0x10c642420102244),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x1da063e4e44d2ca,0x1be763577f4b2dc),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1dc873bdfd08cea,0x4081db17000c8a),(0xffff0000ffff0000ffff0000ffff0000,0xf4b5664c67a182,0x114d5664867a002),(0xffffffff00000000ffffffff00000000,0x3b8047a7ed5720,0x20081047ec5120)]
def h61Steps : List (Nat × Nat × Nat) := [(1,0,1),(3,0,1),(0,1,2),(1,1,2),(2,1,2),(0,2,3),(2,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(0,2,5),(1,2,5),(3,2,5),(1,2,6),(2,2,6),(3,2,6),(1,3,9),(2,3,9),(0,4,5),(2,4,5),(0,4,6),(1,4,6),(2,4,6),(0,4,9),(1,4,9),(2,4,9),(2,5,9),(3,1,2),(0,1,3),(2,1,3),(3,1,3),(0,1,4),(1,1,4),(2,1,4),(3,1,4),(1,0,2),(3,0,2),(1,0,3),(3,0,3),(1,0,4),(2,0,4),(3,0,4),(1,0,7),(1,4,7),(2,4,7),(1,0,50),(2,1,50),(2,2,50),(3,0,8),(0,4,8),(2,4,8),(3,4,8),(1,0,9),(1,0,12),(2,5,12),(1,9,12),(1,0,37),(1,2,37),(2,2,37),(1,1,12),(2,1,12),(1,0,66),(1,0,15),(3,0,15),(1,1,15),(1,0,52),(1,2,52),(2,5,15),(2,4,73),(3,1,17),(1,0,25),(1,2,28),(2,2,28),(3,6,8),(1,0,79),(0,4,59),(1,6,12),(3,20,27),(1,9,33),(2,4,33),(1,2,40),(0,1,59),(3,0,65),(0,2,65),(3,0,70),(3,2,70),(2,1,21),(2,4,21),(1,0,93),(2,1,93),(3,1,77),(1,1,78),(2,1,69),(3,7,41),(3,37,41),(3,1,76),(3,40,41),(2,44,75),(1,1,42),(2,1,42),(2,4,42),(2,1,106),(3,9,43),(0,43,70),(1,7,15),(1,0,55),(1,9,44),(1,33,44),(1,0,85),(0,1,45),(3,7,45),(3,2,45),(2,1,117),(0,8,45),(3,9,45),(3,33,45),(3,37,45),(0,1,63),(3,7,38),(3,15,38),(1,3,91),(2,3,91),(1,7,40),(2,8,37),(2,8,39),(1,9,37),(3,40,63)]
def h61W : BT Decor := buildWiresBT 8 h61Base h61Steps
def h61AutoList : List (List (Nat × Nat)) := [[]]
def h61Autos : BT (List (Nat × Nat)) := btOfList 1 h61AutoList
lemma h61Pairs : goodPairs h61G h61Pos h61Neg := goodPairs_of (by decide +kernel)
lemma h61BaseOk : ∀ x ∈ h61Base, faithful h61Pos h61Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h61WOk : btAll (fun x => faithful h61Pos h61Neg x ∧ x.1 < 2^128) h61W := buildWiresBT_faithful h61BaseOk
lemma h61AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h61G = h61G) h61Autos := btAll_ofList (autos_of (by decide +kernel))
def h61SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,4),some (subcubeFast 0 8,4),some (subcubeFast 0 16,6),some (subcubeFast 0 32,5),some (subcubeFast 1 0,6),some (subcubeFast 1 8,3),some (subcubeFast 1 16,3),some (subcubeFast 1 32,4),some (subcubeFast 8 0,5),some (subcubeFast 8 16,4),some (subcubeFast 16 0,6),some (subcubeFast 32 0,4),some (subcubeFast 32 16,3),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,5),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,5),some (0xff00ff0000ff00ffff00ff0000ff00ff,5),some (0xff00ff00ff00ff00ff00ff00ff00ff0,4),some (0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0,5),some (0xff00ffff00ff0000ff00ffff00ff00,5)]
def h61Slices : BT (Option (Nat × Nat)) := btOfList 5 h61SliceList
def h61Specs : List PoolSpec := poolSteps h61Steps [(4,[]),(0,[]),(7,[]),(13,[]),(5,[]),(8,[]),(4,[3]),(3,[0]),(4,[4]),(2,[0,4]),(2,[0]),(10,[0]),(3,[]),(11,[]),(1,[]),(15,[]),(4,[12]),(10,[]),(2,[]),(4,[13]),(2,[0,13]),(4,[19]),(4,[20]),(18,[]),(3,[1]),(2,[1,4]),(2,[4,1,22]),(4,[22]),(4,[23]),(2,[1]),(10,[1]),(2,[1,22]),(10,[1,22]),(2,[1,23]),(10,[1,23]),(4,[35]),(4,[14]),(10,[1,14]),(4,[16]),(4,[16,88]),(4,[21]),(4,[2]),(2,[2]),(3,[36]),(3,[64]),(2,[4]),(3,[54]),(10,[36]),(2,[36]),(8,[38]),(14,[]),(6,[]),(4,[7]),(4,[10]),(9,[]),(3,[37]),(10,[37]),(2,[37]),(4,[99]),(4,[100]),(4,[101]),(10,[3]),(2,[3]),(12,[]),(3,[38]),(10,[4]),(4,[4,103]),(8,[38,103]),(4,[32]),(10,[32]),(2,[32]),(10,[35]),(2,[35]),(10,[10]),(2,[10]),(8,[39]),(10,[2]),(3,[39]),(4,[2,45]),(10,[2,45]),(4,[4,107]),(4,[28]),(10,[28]),(10,[7]),(2,[40]),(10,[40]),(10,[40,110]),(4,[32,117]),(4,[110]),(17,[]),(4,[112]),(10,[40,112]),(2,[42]),(10,[42]),(2,[2,43]),(16,[]),(3,[63]),(4,[2,44]),(2,[2,44]),(10,[2,44]),(2,[2,45]),(10,[3,50]),(10,[4,28]),(2,[4,34]),(2,[33]),(10,[33]),(2,[34]),(10,[34]),(4,[4,17]),(8,[17]),(4,[4,18]),(8,[18]),(4,[4,26]),(2,[28]),(3,[57]),(10,[32,58]),(4,[33]),(4,[34]),(10,[34,35]),(2,[35,81]),(2,[7]),(2,[7,54]),(2,[7,60]),(2,[7,61]),(4,[8]),(2,[8]),(10,[8]),(4,[9]),(2,[9]),(10,[9]),(10,[10,65])]
def h61Pools : BT (Option BoundPool) := buildPoolsBT 8 h61W h61R h61Slices h61Specs
set_option maxRecDepth 200000 in
lemma h61Slice18 : Slice h61R h61G (0xff00ffff00ff0000ff00ffff00ff00) 5 := opposite_slice (oppositeRow 3 5 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h62Bound
set_option maxRecDepth 200000 in
lemma h61Slice17 : Slice h61R h61G (0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0) 5 := opposite_slice (oppositeRow 2 5 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h63Bound
set_option maxRecDepth 200000 in
lemma h61Slice16 : Slice h61R h61G (0xff00ff00ff00ff00ff00ff00ff00ff0) 4 := opposite_slice (oppositeRow 2 3 41) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
lemma h61Slice15 : Slice h61R h61G (0xff00ff0000ff00ffff00ff0000ff00ff) 5 := mapped_slice (identifyRow 3 5 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h64Bound
set_option maxRecDepth 200000 in
lemma h61Slice14 : Slice h61R h61G (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f) 5 := mapped_slice (identifyRow 2 4 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h65Bound
set_option maxRecDepth 200000 in
lemma h61Slice13 : Slice h61R h61G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 5 := mapped_slice (identifyRow 0 2 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h66Bound
set_option maxRecDepth 200000 in
lemma h61Slice12 : Slice h61R h61G (subcubeFast 32 16) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
lemma h61Slice11 : Slice h61R h61G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h67Bound
set_option maxRecDepth 200000 in
lemma h61Slice10 : Slice h61R h61G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h68Bound
set_option maxRecDepth 200000 in
lemma h61Slice9 : Slice h61R h61G (subcubeFast 8 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h69Bound
set_option maxRecDepth 200000 in
lemma h61Slice8 : Slice h61R h61G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h70Bound
set_option maxRecDepth 200000 in
lemma h61Slice7 : Slice h61R h61G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h71Bound
set_option maxRecDepth 200000 in
lemma h61Slice6 : Slice h61R h61G (subcubeFast 1 16) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h72Bound
set_option maxRecDepth 200000 in
lemma h61Slice5 : Slice h61R h61G (subcubeFast 1 8) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h73Bound
set_option maxRecDepth 200000 in
lemma h61Slice4 : Slice h61R h61G (subcubeFast 1 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h74Bound
set_option maxRecDepth 200000 in
lemma h61Slice3 : Slice h61R h61G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h75Bound
set_option maxRecDepth 200000 in
lemma h61Slice2 : Slice h61R h61G (subcubeFast 0 16) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h76Bound
set_option maxRecDepth 200000 in
lemma h61Slice1 : Slice h61R h61G (subcubeFast 0 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h77Bound
set_option maxRecDepth 200000 in
lemma h61Slice0 : Slice h61R h61G (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h78Bound
lemma h61SlicesOk : btAll (sliceSpec h61R h61G) h61Slices := btAll_ofList (P := sliceSpec h61R h61G) (sliceSpecCons h61Slice0 (sliceSpecCons h61Slice1 (sliceSpecCons h61Slice2 (sliceSpecCons h61Slice3 (sliceSpecCons h61Slice4 (sliceSpecCons h61Slice5 (sliceSpecCons h61Slice6 (sliceSpecCons h61Slice7 (sliceSpecCons h61Slice8 (sliceSpecCons h61Slice9 (sliceSpecCons h61Slice10 (sliceSpecCons h61Slice11 (sliceSpecCons h61Slice12 (sliceSpecCons h61Slice13 (sliceSpecCons h61Slice14 (sliceSpecCons h61Slice15 (sliceSpecCons h61Slice16 (sliceSpecCons h61Slice17 (sliceSpecCons h61Slice18 sliceSpecNil)))))))))))))))))))
set_option maxRecDepth 200000 in
lemma h61PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h61R h61G c) h61Pools := buildPoolsBT_sound h61SlicesOk
def h61Empty : BT (List (List Nat)) := BT.empty
lemma h61EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G (4 - 1) xs.toFinset) h61Empty := trivial
def h61Block4_0 : List NodeSpec := indexPairNodes [(108022827,0), (26483017,0), (7922331,1761), (27345563,1761), (99634219,0), (1728559,0), (478273621,0), (339773495,0), (27394871,0), (285488139,0), (1451237531,0), (128982071,0), (80747575,0), (102832171,16513)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test4_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Empty 4 h61Block4_0 = true := by decide +kernel
def h61Nodes4 : List NodeSpec := h61Block4_0
lemma h61Check4 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Empty 4 h61Nodes4 = true := h61Test4_0
def h61Bucket4 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes4
set_option maxRecDepth 200000 in
lemma h61Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 4 xs.toFinset) h61Bucket4 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61EmptyOk h61Check4
def h61Block5_0 : List NodeSpec := indexPairNodes [(1272,0), (745567,0), (9330,0), (225515,258), (58431,1827), (1007851,0), (532534,0), (231487,0), (778475,465), (569407,64), (2277471,0), (205655,0), (671903,47281), (704671,2769), (729311,2957), (2557355,0), (2688427,0), (9634155,0), (639391,0), (672159,0), (618559,3233), (9394,0), (756923,1697), (2428331,1825), (2559403,1889), (3214523,1697), (606879,12353), (639647,3558409), (860703,12353), (730655,12609), (3506549,64), (3899755,465)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_0 = true := by decide +kernel
def h61Block5_1 : List NodeSpec := indexPairNodes [(3965291,2), (643135,433), (8454507,47313), (3047787,867), (651327,794656), (2228767,0), (2490911,0), (984607,103201), (2229791,111457), (725055,0), (370719,5185), (26143,1889), (51914271,12609), (52962847,0), (9765719,1057), (4096855,5825), (981512279,0), (38012503,6081), (931147883,433), (645935211,0), (790591,0), (595636341,72), (880840811,0), (806975,0), (2867435,0), (830533679,6465), (813764655,0), (245426283,1249), (947916907,497), (9109867,2), (545321007,4260163), (264310831,4522179)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_1 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_1 = true := by decide +kernel
def h61Block5_2 : List NodeSpec := indexPairNodes [(174123115,1249), (749631,16), (774207,0), (847935,8745), (1712175,244917081625), (1124196437,174090125), (230748207,24386073), (39907375,1905027), (9506863,5441), (2393015,0), (61870519,20097), (1714703,53121), (13701167,0), (48304175,0), (193495863,0), (34091831,0), (14202927,0), (1777711,4096225), (612438063,3233), (696324143,0), (1794095,3768545), (9637391,2), (38372751,19585), (180424751,19585), (188813359,0), (222367791,14228395545), (35721263,19585), (14222187,433), (12387179,433), (255869207,0), (14484311,433), (2905119,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_2 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_2 = true := by decide +kernel
def h61Block5_3 : List NodeSpec := indexPairNodes [(921663,64), (11031583,0), (946239,0), (954431,2), (595669109,64), (692115563,22401), (169890847,0), (962623,0), (489503,22657), (717231135,0), (566290539,0), (45353247,23169), (3953695,23169), (938047,8256), (545276183,8), (48328821,433), (2909215,2957), (3113815,0), (3179351,0), (1318999,10881985), (3703639,465), (197148951,1569), (11076439,2539697), (987199,378665), (12648747,465), (8586071,433), (12067871,0), (198719,8745), (213926167,1057), (1019967,852032), (4031319,24961), (200285271,64)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_3 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_3 = true := by decide +kernel
def h61Block5_4 : List NodeSpec := indexPairNodes [(228383,0), (687135,465), (194623,64), (12191319,0), (1028159,0), (1036351,0), (880703,0), (37488215,45573), (55083835,26753), (44254007,5953), (40109655,4), (39585367,624449), (49325335,1057), (2241055,23169), (53519639,1569), (13239895,7105), (3027767,0), (13764183,0), (8061755,32804), (8923183,497), (3946543,497), (8927279,0), (741439,247817), (578900085,0), (788733999,2392289), (905279,0), (165680159,87042225), (49294367,0), (57936159,64), (241231959,0), (237041751,0), (2382749783,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_4 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_4 = true := by decide +kernel
def h61Block5_5 : List NodeSpec := indexPairNodes [(2449858647,0), (42732119,0), (42208855,0), (136326175,465), (16124191,16513), (700460063,64), (775957535,0), (26236971,444899537), (13118495,23169), (684095,0), (692287,433), (260159,0), (708671,794656), (553023,0), (38856811,11473), (138416235,497)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test5_5 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Block5_5 = true := by decide +kernel
def h61Nodes5 : List NodeSpec := h61Block5_0 ++ h61Block5_1 ++ h61Block5_2 ++ h61Block5_3 ++ h61Block5_4 ++ h61Block5_5
lemma h61Check5 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket4 5 h61Nodes5 = true := by
  unfold h61Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h61Test5_0,h61Test5_1⟩,h61Test5_2⟩,h61Test5_3⟩,h61Test5_4⟩,h61Test5_5⟩
def h61Bucket5 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes5
set_option maxRecDepth 200000 in
lemma h61Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 5 xs.toFinset) h61Bucket5 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket4Ok h61Check5
def h61Block6_0 : List NodeSpec := indexPairNodes [(252,30), (382,108), (634,486), (1146,1894), (1150,6212), (266367,8460), (8318,68), (65662,122988), (23679,32878), (13887,1040420), (14911,4055158), (27775,6246), (42047,5087582), (79999,8454), (44095,9290060), (446,122), (698,151799), (702,36), (1210,3180179), (1214,8260731), (450751,117785), (516287,1512219), (1130687,48382605), (8382,24658), (65726,90168), (15935,1695218903), (110783,114), (118975,8260731), (35903,688833609), (46143,17738664029), (25119,3307697), (176351,1647133)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_0 = true := by decide +kernel
def h61Block6_1 : List NodeSpec := indexPairNodes [(26143,28558221), (50239,52110942302), (184543,226558749), (368831,1639979), (2261847,64752751), (8521303,363898407), (4724799,49232), (411711,65135), (725055,843858), (432035903,32854), (585791,843846), (289429567,204478503), (634943,28337423471), (339761215,106562), (536639,40978704949), (8783447,855999351), (5773375,16480), (1329215,24684), (823359,1359257207), (831551,47395937915), (839743,379436206255), (9306671,0xfe33e12113), (9045551,0xe6184b828213), (13643823,983161137227), (3706927,68669683558475), (14949423,0x662624f8684b), (2458415,8281376970827), (9568815,47564636348691), (9307695,0xa51a05018213), (12113967,0x644b0c282c13), (15740975,23402208319563), (9474095,0x511201028584b)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_1 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_1 = true := by decide +kernel
def h61Block6_2 : List NodeSpec := indexPairNodes [(34079791,3594628239115), (15473711,22617437263947), (1262015,8256), (4915519,8196), (4784959,832581209), (6581311,210246695), (8918047,29622839), (913471,173008533675), (798783,9216078), (4000031,21765267), (929855,26911354479), (1327551,24648), (5177663,90124), (5047103,866155755), (7629887,217587309), (11015199,58204727), (8522015,84965707), (182335,0xa20b0f093c5b), (822,209895493), (500159,90176), (516543,464025192233), (1065407,8256), (1098175,24644), (1086,2820591265495), (65846,13474248773), (95263,246156909), (97311,405320632107561), (190527,0xb85188120a5e33), (206911,844022), (1590,66102007), (1933631,0), (2064703,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_2 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_2 = true := by decide +kernel
def h61Block6_3 : List NodeSpec := indexPairNodes [(211007,5292306398247), (6226239,73732), (215103,901158), (6488383,7045), (223295,844406), (3212887,416637272133), (1868607,124272425), (1934143,8875817343957061), (1999679,920672041), (2065215,256931909), (9270,10265606213), (66614,66084069), (574,876774), (886319,0x6b81183190ca19), (951855,481605516823065), (52287,4798637627), (1409855,57408), (56383,3402067443251), (1475391,813873221), (626751,2450078759), (1207359,50817), (1731647,478213), (667711,4900305959), (239679,6392153831575), (106960959,49941318167), (922655,24042177991), (243775,7285271886995), (111155263,81984), (115349567,49216), (149567,293961327), (3082527,59068915309), (1400919,22289621)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_3 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_3 = true := by decide +kernel
def h61Block6_4 : List NodeSpec := indexPairNodes [(1433687,40972), (716863,893006), (205855,4057470010645), (137279,6779395167), (561215,893002), (593983,44562873439), (306202687,957024527), (3605791,5906029), (3344671,1913458473), (675903,6811909751), (390088767,2021750853), (28330047,57412), (227391,9500144602058903), (251967,37658878589991), (256063,38208634403931), (65598,1191542383), (979007,893018), (757823,893006), (766015,612552303), (1044543,2450208939), (528447,5978830077143), (544831,15100214311), (29101631,128466729), (198719,9597287515), (19664447,122948)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test6_4 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Block6_4 = true := by decide +kernel
def h61Nodes6 : List NodeSpec := h61Block6_0 ++ h61Block6_1 ++ h61Block6_2 ++ h61Block6_3 ++ h61Block6_4
lemma h61Check6 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket5 6 h61Nodes6 = true := by
  unfold h61Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h61Test6_0,h61Test6_1⟩,h61Test6_2⟩,h61Test6_3⟩,h61Test6_4⟩
def h61Bucket6 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes6
set_option maxRecDepth 200000 in
lemma h61Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 6 xs.toFinset) h61Bucket6 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket5Ok h61Check6
def h61Block7_0 : List NodeSpec := indexPairNodes [(126,800846), (190,462108843), (153663,2064538827), (157759,3439697099), (323631,19144459), (331823,7947), (170047,6526520883), (178239,27179695307), (318,24758536293939), (574,7215142135), (1086,2820593034899), (60479,0x3f0dc09059c27), (137279,2683901877811), (141375,0x5c7c0f02ce6f), (145471,1449048513739), (149567,3453204642855), (8254,0x25836085049e33), (9791,65834736843), (32830,33118592203), (65598,3608008129683)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test7_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket6 7 h61Block7_0 = true := by decide +kernel
def h61Nodes7 : List NodeSpec := h61Block7_0
lemma h61Check7 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket6 7 h61Nodes7 = true := h61Test7_0
def h61Bucket7 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes7
set_option maxRecDepth 200000 in
lemma h61Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 7 xs.toFinset) h61Bucket7 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket6Ok h61Check7
def h61Block8_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,17,18])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h61Test8_0 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket7 8 h61Block8_0 = true := by decide +kernel
def h61Nodes8 : List NodeSpec := h61Block8_0
lemma h61Check8 : checkNodesBT h61W h61G h61Mask h61Pools h61Autos h61Bucket7 8 h61Nodes8 = true := h61Test8_0
def h61Bucket8 : BT (List (List Nat)) := buildBucketsBT h61W h61Nodes8
set_option maxRecDepth 200000 in
lemma h61Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h61G 8 xs.toFinset) h61Bucket8 := buildBucketsBT_sound (by decide) h61Pairs h61WOk h61PoolsOk h61AutosOk h61Bucket7Ok h61Check8
set_option maxRecDepth 200000 in
lemma h61Bound : Lower h61R h61G 9 := lower_of_forestBT (essPairs := [(VAR 0,0,1),(VAR 2,1,5),(VAR 3,5,13),(VAR 4,12,28),(VAR 5,5,37)]) (by decide +kernel) h61Bucket8Ok (by decide +kernel)
def h79R : List Nat := varsOf 62
def h79G : Nat := 0xfcccfffcf0c0fcccfcccfffcf0c0fccc
lemma h79Bound : Lower h79R h79G 9 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h33R) (T2 := h33G) (by decide +kernel) h33Bound
def h80R : List Nat := varsOf 62
def h80G : Nat := 0xfcffccfcf0ccc0ccfcffccfcf0ccc0cc
lemma h80Bound : Lower h80R h80G 9 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h61R) (T2 := h61G) (by decide +kernel) h61Bound
def h81R : List Nat := varsOf 62
def h81G : Nat := 0xffcfcfccffcccc0cffcfcfccffcccc0c
lemma h81Bound : Lower h81R h81G 9 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h48R) (T2 := h48G) (by decide +kernel) h48Bound
def h83R : List Nat := varsOf 58
def h83G : Nat := 0xffffffff33cc0000ffffffff33cc0000
lemma h83Bound : Lower h83R h83G 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(3,4)]) (roots2 := h62R) (T2 := h62G) (by decide +kernel) h62Bound
def h84R : List Nat := varsOf 54
def h84G : Nat := 0xfffff0f0f3f30000fffff0f0f3f30000
lemma h84Bound : Lower h84R h84G 5 := carry_of (swaps := [(4,5),(0,1),(1,2),(2,3),(3,4),(1,2)]) (roots2 := h52R) (T2 := h52G) (by decide +kernel) h52Bound
def h85R : List Nat := varsOf 58
def h85G : Nat := 0xffffff00ffcc0000ffffff00ffcc0000
lemma h85Bound : Lower h85R h85G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h86R : List Nat := varsOf 30
def h86G : Nat := 0xf3c0f000f3c0f000f3c0f000f3c0f000
lemma h86Bound : Lower h86R h86G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(2,3),(0,1),(1,2)]) (roots2 := h27R) (T2 := h27G) (by decide +kernel) h27Bound
def h87R : List Nat := varsOf 54
def h87G : Nat := 0xfffff0f0c0c00000fffff0f0c0c00000
lemma h87Bound : Lower h87R h87G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(2,3),(0,1),(1,2)]) (roots2 := h24R) (T2 := h24G) (by decide +kernel) h24Bound
def h88R : List Nat := varsOf 58
def h88G : Nat := 0xffffff0033000000ffffff0033000000
lemma h88Bound : Lower h88R h88G 5 := lift_of (z := 2) (o := 0) (essPairs := [(VAR 1,24,26)]) (by decide +kernel) h37Bound
def h89R : List Nat := varsOf 60
def h89G : Nat := 0xfffffff0ff00f000fffffff0ff00f000
lemma h89Bound : Lower h89R h89G 5 := carry_of (swaps := [(2,3),(3,4),(2,3),(0,1),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h90R : List Nat := varsOf 46
def h90G : Nat := 0xfffffffff3c0f3c0fffffffff3c0f3c0
lemma h90Bound : Lower h90R h90G 4 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h31R) (T2 := h31G) (by decide +kernel) h31Bound
def h91R : List Nat := varsOf 60
def h91G : Nat := 0xfffffff0f0f0f000fffffff0f0f0f000
lemma h91Bound : Lower h91R h91G 5 := carry_of (swaps := [(2,3),(3,4),(0,1),(1,2),(2,3),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h82R : List Nat := varsOf 62
def h82G : Nat := 0xfffffff0f3c0f000fffffff0f3c0f000
def h82Pos : List Nat := [12,24,14,22,12,14,24,22,24,40,36,36,48,40,50,22,58,50,50,48,52,48,38,22,30,38,28,42,14,12,36]
def h82Neg : List Nat := [8,26,10,20,4,6,8,18,16,8,4,32,32,32,26,6,26,18,34,20,20,16,6,26,26,34,20,34,26,20,20]
def h82Mask : Nat := fullMask 31
def h82Base : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1bc7c0ac,0x1bc7c0a6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x77d08cbd,0x64588438),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3d012377,0x11814247),(0xffff0000ffff0000ffff0000ffff0000,0x5bfd1ca,0x75bb418a),(0xffffffff00000000ffffffff00000000,0x4a7f7e00,0xa043800)]
def h82Steps : List (Nat × Nat × Nat) := [(0,0,3),(1,1,2),(1,1,3),(1,1,4),(1,2,3),(1,2,4),(3,1,10),(1,3,4),(2,3,5),(1,4,5),(3,2,8),(1,4,13),(1,0,4),(3,4,17),(3,4,6),(3,2,7),(3,1,9),(3,1,12),(3,2,12)]
def h82W : BT Decor := buildWiresBT 5 h82Base h82Steps
def h82AutoList : List (List (Nat × Nat)) := [[]]
def h82Autos : BT (List (Nat × Nat)) := btOfList 1 h82AutoList
lemma h82Pairs : goodPairs h82G h82Pos h82Neg := goodPairs_of (by decide +kernel)
lemma h82BaseOk : ∀ x ∈ h82Base, faithful h82Pos h82Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h82WOk : btAll (fun x => faithful h82Pos h82Neg x ∧ x.1 < 2^128) h82W := buildWiresBT_faithful h82BaseOk
lemma h82AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h82G = h82G) h82Autos := btAll_ofList (autos_of (by decide +kernel))
def h82SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 16,4),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 6 0,4),some (subcubeFast 8 0,5),some (subcubeFast 8 2,4),some (subcubeFast 16 0,4),some (subcubeFast 16 2,4),some (subcubeFast 18 0,4),some (subcubeFast 32 0,5),some (subcubeFast 32 16,3),some (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3,7),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,5),some (0xff0000ffff0000ffff0000ffff0000ff,5),some (0xff00ff00ff00ff00ff00ff00ff00ff0,5)]
def h82Slices : BT (Option (Nat × Nat)) := btOfList 4 h82SliceList
def h82Specs : List PoolSpec := [(12,[]),(2,[]),(0,[]),(3,[(0,0,3)]),(4,[]),(5,[(0,0,3)]),(12,[(0,0,3)]),(7,[]),(10,[(0,0,3)]),(1,[]),(6,[]),(11,[]),(12,[(0,0,3),(2,3,5)]),(3,[(1,0,4)]),(5,[(1,0,4)]),(8,[]),(9,[]),(12,[(1,0,4)]),(10,[]),(12,[(1,0,4),(3,4,17)]),(3,[]),(12,[(1,1,2)]),(5,[]),(13,[]),(15,[]),(12,[(1,1,3)]),(2,[(1,1,3)]),(12,[(1,1,4)]),(0,[(1,2,3)]),(14,[])]
def h82Pools : BT (Option BoundPool) := buildPoolsBT 5 h82W h82R h82Slices h82Specs
set_option maxRecDepth 200000 in
lemma h82Slice15 : Slice h82R h82G (0xff00ff00ff00ff00ff00ff00ff00ff0) 5 := opposite_slice (oppositeRow 2 3 58) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h83Bound
set_option maxRecDepth 200000 in
lemma h82Slice14 : Slice h82R h82G (0xff0000ffff0000ffff0000ffff0000ff) 5 := mapped_slice (identifyRow 3 4 54) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h84Bound
set_option maxRecDepth 200000 in
lemma h82Slice13 : Slice h82R h82G (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f) 5 := mapped_slice (identifyRow 2 4 58) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h85Bound
set_option maxRecDepth 200000 in
lemma h82Slice12 : Slice h82R h82G (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3) 7 := mapped_slice (identifyRow 1 2 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h50Bound
set_option maxRecDepth 200000 in
lemma h82Slice11 : Slice h82R h82G (subcubeFast 32 16) 3 := slice_fast_direct (zDead := 0) (by decide +kernel) h13Bound
set_option maxRecDepth 200000 in
lemma h82Slice10 : Slice h82R h82G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h86Bound
set_option maxRecDepth 200000 in
lemma h82Slice9 : Slice h82R h82G (subcubeFast 18 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h82Slice8 : Slice h82R h82G (subcubeFast 16 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h82Slice7 : Slice h82R h82G (subcubeFast 16 0) 4 := slice_fast_direct (zDead := 2) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h82Slice6 : Slice h82R h82G (subcubeFast 8 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
lemma h82Slice5 : Slice h82R h82G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h87Bound
set_option maxRecDepth 200000 in
lemma h82Slice4 : Slice h82R h82G (subcubeFast 6 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
lemma h82Slice3 : Slice h82R h82G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h88Bound
set_option maxRecDepth 200000 in
lemma h82Slice2 : Slice h82R h82G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h89Bound
set_option maxRecDepth 200000 in
lemma h82Slice1 : Slice h82R h82G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h90Bound
set_option maxRecDepth 200000 in
lemma h82Slice0 : Slice h82R h82G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h91Bound
lemma h82SlicesOk : btAll (sliceSpec h82R h82G) h82Slices := btAll_ofList (P := sliceSpec h82R h82G) (sliceSpecCons h82Slice0 (sliceSpecCons h82Slice1 (sliceSpecCons h82Slice2 (sliceSpecCons h82Slice3 (sliceSpecCons h82Slice4 (sliceSpecCons h82Slice5 (sliceSpecCons h82Slice6 (sliceSpecCons h82Slice7 (sliceSpecCons h82Slice8 (sliceSpecCons h82Slice9 (sliceSpecCons h82Slice10 (sliceSpecCons h82Slice11 (sliceSpecCons h82Slice12 (sliceSpecCons h82Slice13 (sliceSpecCons h82Slice14 (sliceSpecCons h82Slice15 sliceSpecNil))))))))))))))))
set_option maxRecDepth 200000 in
lemma h82PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h82R h82G c) h82Pools := buildPoolsBT_sound h82SlicesOk
def h82Empty : BT (List (List Nat)) := BT.empty
lemma h82EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h82G (4 - 1) xs.toFinset) h82Empty := trivial
def h82Block4_0 : List NodeSpec := nodesWithIdentity [([0,3,6,8,10],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h82Test4_0 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Empty 4 h82Block4_0 = true := by decide +kernel
def h82Nodes4 : List NodeSpec := h82Block4_0
lemma h82Check4 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Empty 4 h82Nodes4 = true := h82Test4_0
def h82Bucket4 : BT (List (List Nat)) := buildBucketsBT h82W h82Nodes4
set_option maxRecDepth 200000 in
lemma h82Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h82G 4 xs.toFinset) h82Bucket4 := buildBucketsBT_sound (by decide) h82Pairs h82WOk h82PoolsOk h82AutosOk h82EmptyOk h82Check4
def h82Block5_0 : List NodeSpec := indexPairNodes [(2172,1280), (32828,812), (16956,1280), (25717,2316), (698,1505), (2230,1377), (15935,12), (33855,0), (2590,1377), (65598,0), (35903,0), (4158,0), (37951,0), (39999,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h82Test5_0 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Bucket4 5 h82Block5_0 = true := by decide +kernel
def h82Nodes5 : List NodeSpec := h82Block5_0
lemma h82Check5 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Bucket4 5 h82Nodes5 = true := h82Test5_0
def h82Bucket5 : BT (List (List Nat)) := buildBucketsBT h82W h82Nodes5
set_option maxRecDepth 200000 in
lemma h82Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h82G 5 xs.toFinset) h82Bucket5 := buildBucketsBT_sound (by decide) h82Pairs h82WOk h82PoolsOk h82AutosOk h82Bucket4Ok h82Check5
def h82Block6_0 : List NodeSpec := indexPairNodes [(124,1020), (16444,14636), (27765,1034508), (29813,1706284), (190,65539370), (318,229315882), (574,329782570), (1086,1621761292), (2110,1118313740), (8254,11142412)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h82Test6_0 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Bucket5 6 h82Block6_0 = true := by decide +kernel
def h82Nodes6 : List NodeSpec := h82Block6_0
lemma h82Check6 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Bucket5 6 h82Nodes6 = true := h82Test6_0
def h82Bucket6 : BT (List (List Nat)) := buildBucketsBT h82W h82Nodes6
set_option maxRecDepth 200000 in
lemma h82Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h82G 6 xs.toFinset) h82Bucket6 := buildBucketsBT_sound (by decide) h82Pairs h82WOk h82PoolsOk h82AutosOk h82Bucket5Ok h82Check6
def h82Block7_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0,1,2,16,18,20,22])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h82Test7_0 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Bucket6 7 h82Block7_0 = true := by decide +kernel
def h82Nodes7 : List NodeSpec := h82Block7_0
lemma h82Check7 : checkNodesBT h82W h82G h82Mask h82Pools h82Autos h82Bucket6 7 h82Nodes7 = true := h82Test7_0
def h82Bucket7 : BT (List (List Nat)) := buildBucketsBT h82W h82Nodes7
set_option maxRecDepth 200000 in
lemma h82Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h82G 7 xs.toFinset) h82Bucket7 := buildBucketsBT_sound (by decide) h82Pairs h82WOk h82PoolsOk h82AutosOk h82Bucket6Ok h82Check7
set_option maxRecDepth 200000 in
lemma h82Bound : Lower h82R h82G 8 := lower_of_forestBT (essPairs := [(VAR 1,20,22),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,6,22),(VAR 5,4,36)]) (by decide +kernel) h82Bucket7Ok (by decide +kernel)
namespace Cofactor12116

def R_23 : List Nat := varsOf 46
def G_23 : Nat := 0xfffcfffcfcc0fcc0fffcfffcfcc0fcc0
lemma low_23 : Lower R_23 G_23 7 := carry_of (swaps := [(4,5),(2,3),(1,2),(0,1)]) (roots2 := Cofactor12068.R_7) (T2 := Cofactor12068.G_7) (by decide +kernel) Cofactor12068.low_7

def G_46 : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
def R_46 : List Nat := varsOf 39
lemma low_46_ok : carryOK [(0,3),(0,2),(0,1)] R_46 G_46 R_23 G_23 = true := by decide +kernel
lemma low_46 : Lower R_46 G_46 7 := carry_of low_46_ok low_23

def G_59 : Nat := 0xfefee8e8e8e8e8e8fefee8e8e8e8e8e8
def R_59 : List Nat := varsOf 55
lemma low_59_ok : liftCheck 0 16 R_59 G_59 R_46 G_46 [(VAR 4,49,33)] = true := by decide +kernel
lemma low_59 : Lower R_59 G_59 8 := lift_of low_59_ok low_46

end Cofactor12116
def h92R : List Nat := varsOf 47
def h92G : Nat := 0xfeeefeeee888e888feeefeeee888e888
lemma h92Bound : Lower h92R h92G 8 := carry_of (swaps := [(2,3),(3,4),(4,5),(2,3),(3,4)]) (roots2 := Cofactor12116.R_59) (T2 := Cofactor12116.G_59) (by decide +kernel) Cofactor12116.low_59
def h94R : List Nat := varsOf 54
def h94G : Nat := 0xfcfcfcfcf0f0ccccfcfcfcfcf0f0cccc
lemma h94Bound : Lower h94R h94G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(1,2)]) (roots2 := h12R) (T2 := h12G) (by decide +kernel) h12Bound
def h95R : List Nat := varsOf 39
def h95G : Nat := 0xfefefefe88888888fefefefe88888888
lemma h95Bound : Lower h95R h95G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(3,4),(2,3),(1,2)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h96R : List Nat := varsOf 53
def h96G : Nat := 0xffffa0a0fafa0000ffffa0a0fafa0000
lemma h96Bound : Lower h96R h96G 6 := carry_of (swaps := [(3,4)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h97R : List Nat := varsOf 54
def h97G : Nat := 0xfffffcfcf0f00000fffffcfcf0f00000
lemma h97Bound : Lower h97R h97G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(4,5),(0,1),(1,2),(0,1)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h98R : List Nat := varsOf 54
def h98G : Nat := 0xfcfcf0f0f0f0c0c0fcfcf0f0f0f0c0c0
lemma h98Bound : Lower h98R h98G 6 := carry_of (swaps := [(2,3),(3,4),(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h99R : List Nat := varsOf 23
def h99G : Nat := 0xfafa8888fafa8888fafa8888fafa8888
lemma h99Bound : Lower h99R h99G 4 := carry_of (swaps := [(4,5),(3,4),(1,2),(2,3),(1,2)]) (roots2 := h46R) (T2 := h46G) (by decide +kernel) h46Bound
def h100R : List Nat := varsOf 39
def h100G : Nat := 0xe8e8e8e888888888e8e8e8e888888888
lemma h100Bound : Lower h100R h100G 5 := lift_of (z := 0) (o := 4) (essPairs := [(VAR 2,33,37)]) (by decide +kernel) h15Bound
def h101R : List Nat := varsOf 19
def h101G : Nat := 0xeeee8888eeee8888eeee8888eeee8888
lemma h101Bound : Lower h101R h101G 4 := carry_of (swaps := [(4,5),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h102R : List Nat := varsOf 51
def h102G : Nat := 0xeeee8888aaaa8888eeee8888aaaa8888
lemma h102Bound : Lower h102R h102G 5 := carry_of (swaps := [(2,3),(3,4),(0,1)]) (roots2 := h24R) (T2 := h24G) (by decide +kernel) h24Bound
def h103R : List Nat := varsOf 53
def h103G : Nat := 0xfafaa0a0fafa0000fafaa0a0fafa0000
lemma h103Bound : Lower h103R h103G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(1,2)]) (roots2 := h24R) (T2 := h24G) (by decide +kernel) h24Bound
def h104R : List Nat := varsOf 22
def h104G : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
lemma h104Bound : Lower h104R h104G 4 := carry_of (swaps := [(4,5),(1,2),(2,3)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h105R : List Nat := varsOf 54
def h105G : Nat := 0xfcfcc0c0f0f00000fcfcc0c0f0f00000
lemma h105Bound : Lower h105R h105G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1),(1,2),(0,1)]) (roots2 := h100R) (T2 := h100G) (by decide +kernel) h100Bound
def h106R : List Nat := varsOf 23
def h106G : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
lemma h106Bound : Lower h106R h106G 7 := Cofactor12068.low_7
def h107R : List Nat := varsOf 51
def h107G : Nat := 0xffffeeeeffff8888ffffeeeeffff8888
lemma h107Bound : Lower h107R h107G 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h93R : List Nat := varsOf 55
def h93G : Nat := 0xfefee8e8fafa8888fefee8e8fafa8888
def h93Pos : List Nat := [17,38,17,20,37,37,20,17,38,37,3,50,22,22,3,21,50,17,35,7,3,20,7,49,19,38,35,50,21,52,37,17,49,3,3,7,21,19,49,3,17,7]
def h93Neg : List Nat := [16,36,18,16,33,36,4,1,6,5,2,48,18,6,1,5,18,5,34,6,18,0,5,33,18,34,33,34,1,36,1,33,1,0,6,2,16,1,48,5,0,1]
def h93Mask : Nat := fullMask 42
def h93Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3ffd5dec6b5,0x2a1d4c2c290),(0xcccccccccccccccccccccccccccccccc,0x2ae0f5d7d02,0xc0b1d3504),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x2187268b37a,0x84204aa362),(0xffff0000ffff0000ffff0000ffff0000,0x171b9a3b8cd,0x500111180d),(0xffffffff00000000ffffffff00000000,0x416e850b32,0x40ae840832)]
def h93Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(0,1,2),(1,1,2),(2,1,2),(2,1,3),(0,2,3),(1,0,20),(1,2,3),(2,2,3),(3,2,3),(1,2,5),(2,2,5),(1,3,5),(0,1,27),(0,2,27),(1,2,27),(2,2,27),(3,2,27),(2,3,5),(2,4,5),(1,5,20),(3,0,22),(1,3,36),(0,4,22),(1,5,38),(3,5,22),(1,5,24),(2,4,29),(0,4,30),(3,3,6),(0,4,6),(1,2,45),(2,2,45),(1,3,45),(2,3,45),(2,22,45),(0,6,22),(2,6,24),(0,2,48),(3,2,48),(1,3,7),(1,7,24),(1,3,9),(0,4,10),(2,4,11),(0,4,14),(2,4,14),(1,12,19),(1,1,13),(2,1,13),(2,4,13),(1,0,16),(3,3,66),(2,14,16),(0,4,17),(1,0,18)]
def h93W : BT Decor := buildWiresBT 7 h93Base h93Steps
def h93AutoList : List (List (Nat × Nat)) := [[],[(1,2),(0,4)]]
def h93Autos : BT (List (Nat × Nat)) := btOfList 1 h93AutoList
lemma h93Pairs : goodPairs h93G h93Pos h93Neg := goodPairs_of (by decide +kernel)
lemma h93BaseOk : ∀ x ∈ h93Base, faithful h93Pos h93Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h93WOk : btAll (fun x => faithful h93Pos h93Neg x ∧ x.1 < 2^128) h93W := buildWiresBT_faithful h93BaseOk
lemma h93AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h93G = h93G) h93Autos := btAll_ofList (autos_of (by decide +kernel))
def h93SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 32,7),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 2 32,4),some (subcubeFast 4 0,5),some (subcubeFast 4 32,4),some (subcubeFast 16 0,5),some (subcubeFast 16 4,4),some (subcubeFast 32 0,4),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,6),some (0xaaaaaaaa55555555aaaaaaaa55555555,5),some (0xcccc3333cccc3333cccc3333cccc3333,6),some (0xffff00000000ffffffff00000000ffff,5),some (0x5555aaaa5555aaaa5555aaaa5555aaaa,5)]
def h93Slices : BT (Option (Nat × Nat)) := btOfList 5 h93SliceList
def h93Specs : List PoolSpec := poolSteps h93Steps [(3,[]),(6,[]),(2,[0]),(13,[]),(8,[]),(10,[]),(2,[15,16]),(0,[]),(1,[]),(2,[15]),(0,[29]),(5,[]),(12,[]),(15,[]),(2,[]),(0,[22]),(2,[0,22]),(2,[17]),(8,[33]),(10,[33]),(2,[18]),(11,[]),(2,[19]),(2,[0,20]),(2,[0,21]),(16,[]),(2,[0,28]),(4,[]),(2,[1]),(15,[1]),(1,[14]),(15,[1,40]),(3,[40]),(7,[]),(2,[1,14]),(6,[40]),(2,[2]),(2,[2,50]),(2,[3]),(2,[4]),(13,[52]),(2,[4,52]),(2,[5]),(2,[6]),(8,[54]),(1,[9]),(17,[]),(2,[7]),(9,[]),(2,[8]),(2,[8,58]),(2,[8,59]),(2,[9]),(15,[9]),(14,[]),(2,[10]),(2,[11]),(2,[11,61]),(2,[12]),(6,[64]),(8,[64]),(2,[13])]
def h93Pools : BT (Option BoundPool) := buildPoolsBT 6 h93W h93R h93Slices h93Specs
set_option maxRecDepth 200000 in
lemma h93Slice17 : Slice h93R h93G (0x5555aaaa5555aaaa5555aaaa5555aaaa) 5 := opposite_slice (oppositeRow 0 4 54) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h94Bound
set_option maxRecDepth 200000 in
lemma h93Slice16 : Slice h93R h93G (0xffff00000000ffffffff00000000ffff) 5 := mapped_slice (identifyRow 4 5 39) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h95Bound
set_option maxRecDepth 200000 in
lemma h93Slice15 : Slice h93R h93G (0xcccc3333cccc3333cccc3333cccc3333) 6 := mapped_slice (identifyRow 1 4 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h96Bound
set_option maxRecDepth 200000 in
lemma h93Slice14 : Slice h93R h93G (0xaaaaaaaa55555555aaaaaaaa55555555) 5 := mapped_slice (identifyRow 0 5 54) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h97Bound
set_option maxRecDepth 200000 in
lemma h93Slice13 : Slice h93R h93G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 6 := mapped_slice (identifyRow 0 2 54) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h98Bound
set_option maxRecDepth 200000 in
lemma h93Slice12 : Slice h93R h93G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h99Bound
set_option maxRecDepth 200000 in
lemma h93Slice11 : Slice h93R h93G (subcubeFast 16 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
lemma h93Slice10 : Slice h93R h93G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h100Bound
set_option maxRecDepth 200000 in
lemma h93Slice9 : Slice h93R h93G (subcubeFast 4 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h101Bound
set_option maxRecDepth 200000 in
lemma h93Slice8 : Slice h93R h93G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h102Bound
set_option maxRecDepth 200000 in
lemma h93Slice7 : Slice h93R h93G (subcubeFast 2 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
lemma h93Slice6 : Slice h93R h93G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h103Bound
set_option maxRecDepth 200000 in
lemma h93Slice5 : Slice h93R h93G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h104Bound
set_option maxRecDepth 200000 in
lemma h93Slice4 : Slice h93R h93G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
lemma h93Slice3 : Slice h93R h93G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h105Bound
set_option maxRecDepth 200000 in
lemma h93Slice2 : Slice h93R h93G (subcubeFast 0 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h106Bound
set_option maxRecDepth 200000 in
lemma h93Slice1 : Slice h93R h93G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h107Bound
set_option maxRecDepth 200000 in
lemma h93Slice0 : Slice h93R h93G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h55Bound
lemma h93SlicesOk : btAll (sliceSpec h93R h93G) h93Slices := btAll_ofList (P := sliceSpec h93R h93G) (sliceSpecCons h93Slice0 (sliceSpecCons h93Slice1 (sliceSpecCons h93Slice2 (sliceSpecCons h93Slice3 (sliceSpecCons h93Slice4 (sliceSpecCons h93Slice5 (sliceSpecCons h93Slice6 (sliceSpecCons h93Slice7 (sliceSpecCons h93Slice8 (sliceSpecCons h93Slice9 (sliceSpecCons h93Slice10 (sliceSpecCons h93Slice11 (sliceSpecCons h93Slice12 (sliceSpecCons h93Slice13 (sliceSpecCons h93Slice14 (sliceSpecCons h93Slice15 (sliceSpecCons h93Slice16 (sliceSpecCons h93Slice17 sliceSpecNil))))))))))))))))))
set_option maxRecDepth 200000 in
lemma h93PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h93R h93G c) h93Pools := buildPoolsBT_sound h93SlicesOk
def h93Empty : BT (List (List Nat)) := BT.empty
lemma h93EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h93G (4 - 1) xs.toFinset) h93Empty := trivial
def h93Block4_0 : List NodeSpec := indexPairNodes [(6828117,0), (7083061,0), (19984469,0), (1512207,0), (74783,0), (2036495,0), (4330255,0), (97311,0), (17868823,0), (19965975,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test4_0 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Empty 4 h93Block4_0 = true := by decide +kernel
def h93Nodes4 : List NodeSpec := h93Block4_0
lemma h93Check4 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Empty 4 h93Nodes4 = true := h93Test4_0
def h93Bucket4 : BT (List (List Nat)) := buildBucketsBT h93W h93Nodes4
set_option maxRecDepth 200000 in
lemma h93Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h93G 4 xs.toFinset) h93Bucket4 := buildBucketsBT_sound (by decide) h93Pairs h93WOk h93PoolsOk h93AutosOk h93EmptyOk h93Check4
def h93Block5_0 : List NodeSpec := indexPairNodes [(135413,240), (3802655,7367), (64575,57360), (258293,512), (2893871,6865), (3280415,913), (548959,951345), (149567,5411), (2373679,16), (3019295,0), (935983,0), (2758175,0), (153663,867), (686127,14919), (948271,13667), (2390063,0), (2914351,0), (27788331,462865), (12324383,433), (194623,2737), (45103151,256), (11801119,0), (11277855,233489), (198719,0), (218143,433), (676895,0), (939039,0), (2380831,176145), (182335,800), (215103,0), (239679,0), (55055477,20)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test5_0 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket4 5 h93Block5_0 = true := by decide +kernel
def h93Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,68],[]),([0,1,2,3,4,67],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test5_1 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket4 5 h93Block5_1 = true := by decide +kernel
def h93Nodes5 : List NodeSpec := h93Block5_0 ++ h93Block5_1
lemma h93Check5 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket4 5 h93Nodes5 = true := by
  unfold h93Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h93Test5_0,h93Test5_1⟩
def h93Bucket5 : BT (List (List Nat)) := buildBucketsBT h93W h93Nodes5
set_option maxRecDepth 200000 in
lemma h93Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h93G 5 xs.toFinset) h93Bucket5 := buildBucketsBT_sound (by decide) h93Pairs h93WOk h93PoolsOk h93AutosOk h93Bucket4Ok h93Check5
def h93Block6_0 : List NodeSpec := indexTripleNodes [(31871,1902,6), (71807,263038,2), (75903,6308450,2), (79999,238459,2), (88151,508695,2), (92247,42039,2), (96303,14919,2), (48191,67297826,6), (120879,176167,2), (32287,6543,2), (221547,255988903,2), (270527,12071185,6), (286911,967369,2), (303295,8405796,2), (165951,335602466,6), (87071,949947409,6), (170047,604013414,2), (270783,885267,2), (287167,530,2), (211007,6725773075,2), (508223,192677,2), (219199,31695886779,2), (223295,300729837861,2), (115743,3256760731,2), (41022,26610825,2), (492095,30461605,2), (137279,92362347451,2), (487531,78663987,2), (495723,761895,2), (128031,755964467,2), (84543,10095319,6), (1903167,445024883,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test6_0 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket5 6 h93Block6_0 = true := by decide +kernel
def h93Block6_1 : List NodeSpec := indexPairNodes [(231487,1369482615), (235583,331475209), (32830,5477967003), (256063,0xe1070b0b897), (272415,273846503697), (536639,0x92e089ce227), (544831,1891187070103)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test6_1 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket5 6 h93Block6_1 = true := by decide +kernel
def h93Nodes6 : List NodeSpec := h93Block6_0 ++ h93Block6_1
lemma h93Check6 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket5 6 h93Nodes6 = true := by
  unfold h93Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h93Test6_0,h93Test6_1⟩
def h93Bucket6 : BT (List (List Nat)) := buildBucketsBT h93W h93Nodes6
set_option maxRecDepth 200000 in
lemma h93Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h93G 6 xs.toFinset) h93Bucket6 := buildBucketsBT_sound (by decide) h93Pairs h93WOk h93PoolsOk h93AutosOk h93Bucket5Ok h93Check6
def h93Block7_0 : List NodeSpec := indexTripleNodes [(126,53886,2), (190,805356406,6), (318,377842391,6), (574,6197267159,6), (1086,13468312279,2), (2110,33373637335,2), (4158,141909256919,2), (8254,225573423831,6), (9791,48364874455,6), (32830,7177065646807,6), (65598,489976851159,2), (12863,3232587424471,6), (13887,270758234839,2), (14911,7839564352215,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test7_0 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket6 7 h93Block7_0 = true := by decide +kernel
def h93Nodes7 : List NodeSpec := h93Block7_0
lemma h93Check7 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket6 7 h93Nodes7 = true := h93Test7_0
def h93Bucket7 : BT (List (List Nat)) := buildBucketsBT h93W h93Nodes7
set_option maxRecDepth 200000 in
lemma h93Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h93G 7 xs.toFinset) h93Bucket7 := buildBucketsBT_sound (by decide) h93Pairs h93WOk h93PoolsOk h93AutosOk h93Bucket6Ok h93Check7
def h93Block8_0 : List NodeSpec := [([0,1,2,3,4],[14],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h93Test8_0 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket7 8 h93Block8_0 = true := by decide +kernel
def h93Nodes8 : List NodeSpec := h93Block8_0
lemma h93Check8 : checkNodesBT h93W h93G h93Mask h93Pools h93Autos h93Bucket7 8 h93Nodes8 = true := h93Test8_0
def h93Bucket8 : BT (List (List Nat)) := buildBucketsBT h93W h93Nodes8
set_option maxRecDepth 200000 in
lemma h93Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h93G 8 xs.toFinset) h93Bucket8 := buildBucketsBT_sound (by decide) h93Pairs h93WOk h93PoolsOk h93AutosOk h93Bucket7Ok h93Check8
set_option maxRecDepth 200000 in
lemma h93Bound : Lower h93R h93G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,16,20),(VAR 4,1,17),(VAR 5,5,37)]) (by decide +kernel) h93Bucket8Ok (by decide +kernel)
def h108R : List Nat := varsOf 59
def h108G : Nat := 0xffeeee88ffcc8888ffeeee88ffcc8888
lemma h108Bound : Lower h108R h108G 9 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h93R) (T2 := h93G) (by decide +kernel) h93Bound
def h110R : List Nat := varsOf 53
def h110G : Nat := 0xfffffafafafa0000fffffafafafa0000
lemma h110Bound : Lower h110R h110G 5 := carry_of (swaps := [(3,4)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h111R : List Nat := varsOf 29
def h111G : Nat := 0xfa00a000fa00a000fa00a000fa00a000
lemma h111Bound : Lower h111R h111G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,5,13)]) (by decide +kernel) h51Bound
def h112R : List Nat := varsOf 45
def h112G : Nat := 0xfffafffaa000a000fffafffaa000a000
lemma h112Bound : Lower h112R h112G 6 := carry_of (swaps := [(3,4),(4,5),(3,4)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h113R : List Nat := varsOf 57
def h113G : Nat := 0xffffffaaaa000000ffffffaaaa000000
lemma h113Bound : Lower h113R h113G 6 := carry_of (swaps := [(3,4),(4,5),(2,3)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h114R : List Nat := varsOf 60
def h114G : Nat := 0xfffffff0f0000000fffffff0f0000000
lemma h114Bound : Lower h114R h114G 6 := carry_of (swaps := [(3,4),(4,5),(2,3),(0,1),(1,2)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h115R : List Nat := varsOf 53
def h115G : Nat := 0xfffffffffafaa0a0fffffffffafaa0a0
lemma h115Bound : Lower h115R h115G 5 := carry_of (swaps := [(0,1),(1,2),(2,3),(3,4),(4,5),(0,1)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h109R : List Nat := varsOf 61
def h109G : Nat := 0xfffffffafa00a000fffffffafa00a000
def h109Pos : List Nat := [25,28,13,13,28,13,25,25,29,40,33,33,13,48,48,28,44,40,36,25,40,36,41,52,37,48,41,36,49,40,49,13,52,25,40,29,33,48,49,13,33,28,13,13,33,41,56,36,25]
def h109Neg : List Nat := [24,24,9,12,20,5,17,9,21,8,1,32,0,16,32,12,12,32,4,16,12,32,32,20,5,21,9,12,17,9,32,21,32,1,0,24,17,0,1,8,0,21,4,1,5,8,24,5,21]
def h109Mask : Nat := fullMask 49
def h109Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x13ddad5481ded,0x19a52b70005e4),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x8e8989a5913e,0x196008b958138),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x16e8ea45b93ff,0x60882c11828f),(0xffff0000ffff0000ffff0000ffff0000,0x1426b5288e1d3,0x1421892882153),(0xffffffff00000000ffffffff00000000,0xf1757ff76e00,0x140624800)]
def h109Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(1,0,2),(3,0,2),(0,1,2),(3,1,2),(1,2,3),(2,2,3),(1,2,4),(2,2,4),(3,2,4),(0,2,6),(1,2,6),(2,2,6),(3,2,6),(1,3,4),(3,3,4),(1,3,6),(3,3,6),(1,3,9),(3,3,9),(0,4,6),(1,4,6),(2,4,6),(3,4,6),(1,4,9),(3,4,9),(1,1,3),(0,2,33),(1,6,26),(3,3,33),(3,9,33),(3,1,3),(1,1,4),(3,9,39),(1,6,40),(1,1,9),(3,3,42),(3,4,42),(0,6,15),(1,3,17),(1,4,17),(1,3,20),(3,1,23),(0,2,23),(3,4,23),(2,2,24),(1,4,24),(3,6,25),(3,1,31),(1,1,32),(2,2,32),(1,0,3),(0,2,28),(2,2,30),(3,3,58),(0,39,58),(3,1,28),(1,1,59),(3,3,28),(1,3,30),(1,0,4),(3,3,67),(2,2,63),(1,3,63),(1,6,68),(1,2,27),(1,3,27),(3,0,4),(3,0,12),(2,12,24),(0,6,12),(2,6,13),(1,0,19),(1,4,19),(1,0,16),(3,1,81),(1,16,17),(3,3,41),(2,6,16),(3,0,18),(3,1,18),(3,17,18),(1,5,76),(0,6,21),(3,6,21),(1,0,22),(2,6,22),(3,0,23),(3,0,28),(3,27,28),(1,1,95),(1,0,29),(1,3,87),(3,3,97)]
def h109W : BT Decor := buildWiresBT 7 h109Base h109Steps
def h109AutoList : List (List (Nat × Nat)) := [[],[(2,4)],[(0,2)],[(0,4)],[(2,4),(0,2)],[(2,4),(0,4)]]
def h109Autos : BT (List (Nat × Nat)) := btOfList 3 h109AutoList
lemma h109Pairs : goodPairs h109G h109Pos h109Neg := goodPairs_of (by decide +kernel)
lemma h109BaseOk : ∀ x ∈ h109Base, faithful h109Pos h109Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h109WOk : btAll (fun x => faithful h109Pos h109Neg x ∧ x.1 < 2^128) h109W := buildWiresBT_faithful h109BaseOk
lemma h109AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h109G = h109G) h109Autos := btAll_ofList (autos_of (by decide +kernel))
def h109SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,5),some (subcubeFast 1 0,6),some (subcubeFast 4 0,6),some (subcubeFast 16 0,6),some (subcubeFast 32 0,5),some (subcubeFast 32 8,4),some (0xaa55aa55aa55aa55aa55aa55aa55aa55,5),some (0xf00ff00ff00ff00ff00ff00ff00ff00f,5),some (0xff0000ffff0000ffff0000ffff0000ff,5),some (0x55555555aaaaaaaa55555555aaaaaaaa,5),some (0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0,5),some (0xff00ffff00ff0000ff00ffff00ff00,7),some (0xffffffff00000000ffffffff0000,5)]
def h109Slices : BT (Option (Nat × Nat)) := btOfList 4 h109SliceList
def h109Specs : List PoolSpec := poolSteps h109Steps [(1,[]),(2,[]),(2,[4]),(11,[1,4]),(0,[]),(2,[4,20]),(4,[4]),(2,[53]),(3,[]),(1,[28]),(3,[1]),(2,[62]),(0,[62]),(0,[27]),(4,[]),(2,[62,63]),(1,[7]),(6,[]),(1,[8]),(8,[]),(1,[21,30]),(1,[8,73]),(11,[1]),(1,[10]),(5,[]),(1,[11]),(1,[12]),(2,[12]),(11,[1,12]),(12,[]),(1,[12,13]),(1,[13]),(1,[14]),(2,[14]),(11,[1,14]),(1,[15]),(1,[15,43]),(1,[16]),(1,[16,85]),(9,[]),(1,[16,86]),(1,[17]),(1,[18]),(2,[18]),(1,[19]),(2,[19]),(1,[22]),(1,[22,67]),(1,[22,68]),(1,[23]),(2,[23]),(1,[23,54]),(2,[23,54]),(1,[23,60]),(1,[24]),(1,[25]),(2,[25]),(2,[3]),(3,[3]),(2,[13]),(7,[]),(3,[4]),(10,[]),(1,[37]),(3,[4,37]),(11,[4,37]),(11,[4]),(0,[26]),(1,[26]),(1,[27]),(3,[62]),(2,[69]),(3,[69]),(11,[]),(2,[10]),(3,[10]),(2,[11]),(3,[11])]
def h109Pools : BT (Option BoundPool) := buildPoolsBT 7 h109W h109R h109Slices h109Specs
set_option maxRecDepth 200000 in
lemma h109Slice12 : Slice h109R h109G (0xffffffff00000000ffffffff0000) 5 := opposite_slice (oppositeRow 4 5 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h17Bound
set_option maxRecDepth 200000 in
lemma h109Slice11 : Slice h109R h109G (0xff00ffff00ff0000ff00ffff00ff00) 7 := opposite_slice (oppositeRow 3 5 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h49Bound
set_option maxRecDepth 200000 in
lemma h109Slice10 : Slice h109R h109G (0xf0f0f0ff0f0f0f00f0f0f0ff0f0f0f0) 5 := opposite_slice (oppositeRow 2 5 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h63Bound
set_option maxRecDepth 200000 in
lemma h109Slice9 : Slice h109R h109G (0x55555555aaaaaaaa55555555aaaaaaaa) 5 := opposite_slice (oppositeRow 0 5 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h89Bound
set_option maxRecDepth 200000 in
lemma h109Slice8 : Slice h109R h109G (0xff0000ffff0000ffff0000ffff0000ff) 5 := mapped_slice (identifyRow 3 4 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h110Bound
set_option maxRecDepth 200000 in
lemma h109Slice7 : Slice h109R h109G (0xf00ff00ff00ff00ff00ff00ff00ff00f) 5 := mapped_slice (identifyRow 2 3 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h63Bound
set_option maxRecDepth 200000 in
lemma h109Slice6 : Slice h109R h109G (0xaa55aa55aa55aa55aa55aa55aa55aa55) 5 := mapped_slice (identifyRow 0 3 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h89Bound
set_option maxRecDepth 200000 in
lemma h109Slice5 : Slice h109R h109G (subcubeFast 32 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
lemma h109Slice4 : Slice h109R h109G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h111Bound
set_option maxRecDepth 200000 in
lemma h109Slice3 : Slice h109R h109G (subcubeFast 16 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h112Bound
set_option maxRecDepth 200000 in
lemma h109Slice2 : Slice h109R h109G (subcubeFast 4 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h113Bound
set_option maxRecDepth 200000 in
lemma h109Slice1 : Slice h109R h109G (subcubeFast 1 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h114Bound
set_option maxRecDepth 200000 in
lemma h109Slice0 : Slice h109R h109G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h115Bound
lemma h109SlicesOk : btAll (sliceSpec h109R h109G) h109Slices := btAll_ofList (P := sliceSpec h109R h109G) (sliceSpecCons h109Slice0 (sliceSpecCons h109Slice1 (sliceSpecCons h109Slice2 (sliceSpecCons h109Slice3 (sliceSpecCons h109Slice4 (sliceSpecCons h109Slice5 (sliceSpecCons h109Slice6 (sliceSpecCons h109Slice7 (sliceSpecCons h109Slice8 (sliceSpecCons h109Slice9 (sliceSpecCons h109Slice10 (sliceSpecCons h109Slice11 (sliceSpecCons h109Slice12 sliceSpecNil)))))))))))))
set_option maxRecDepth 200000 in
lemma h109PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h109R h109G c) h109Pools := buildPoolsBT_sound h109SlicesOk
def h109Empty : BT (List (List Nat)) := BT.empty
lemma h109EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G (3 - 1) xs.toFinset) h109Empty := trivial
def h109Block3_0 : List NodeSpec := nodesWithIdentity [([4,33,58,59],[]),([2,4,6,89],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test3_0 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Empty 3 h109Block3_0 = true := by decide +kernel
def h109Nodes3 : List NodeSpec := h109Block3_0
lemma h109Check3 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Empty 3 h109Nodes3 = true := h109Test3_0
def h109Bucket3 : BT (List (List Nat)) := buildBucketsBT h109W h109Nodes3
set_option maxRecDepth 200000 in
lemma h109Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G 3 xs.toFinset) h109Bucket3 := buildBucketsBT_sound (by decide) h109Pairs h109WOk h109PoolsOk h109AutosOk h109EmptyOk h109Check3
def h109Block4_0 : List NodeSpec := indexPairNodes [(6691145,0), (31605037,4), (516285,4), (1130685,0), (6845377581,0), (1712097325,512), (428255277,0), (1851581,2), (1941669,0), (99619145,0), (32247351,0), (1302615,0), (1318959,0), (1384535,0), (32770615,0), (118490167,0), (4620717,0), (383007,0), (5943349293,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test4_0 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket3 4 h109Block4_0 = true := by decide +kernel
def h109Nodes4 : List NodeSpec := h109Block4_0
lemma h109Check4 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket3 4 h109Nodes4 = true := h109Test4_0
def h109Bucket4 : BT (List (List Nat)) := buildBucketsBT h109W h109Nodes4
set_option maxRecDepth 200000 in
lemma h109Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G 4 xs.toFinset) h109Bucket4 := buildBucketsBT_sound (by decide) h109Pairs h109WOk h109PoolsOk h109AutosOk h109Bucket3Ok h109Check4
def h109Block5_0 : List NodeSpec := indexTripleNodes [(5304,6,2), (3214525,0,2), (4000957,6,2), (8785085,4,2), (66740,0,2), (263348,0,2), (2098356,0,2), (951925,32,2), (1017461,0,2), (639349,68,2), (672117,4,2), (835957,4,2), (868725,4,2), (428196141,1798,30), (654360765,0,18), (159760573,6,2), (43527285,512,66), (63998069,512,2), (59811957,512,2), (956350653,6,2), (38584509,4,2), (3375477,3205,2), (186660981,497,2), (182470773,0,2), (4096373,3717,2), (679567797,0,2), (629285301,0,2), (9109877,4,2), (270390,0,2), (3277871,1185,2), (602175,0,2), (206911,38961,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test5_0 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket4 5 h109Block5_0 = true := by decide +kernel
def h109Block5_1 : List NodeSpec := indexTripleNodes [(278582,512,82), (64575,51249,2), (610367,35895,82), (597079,497,2), (170047,0,2), (9896309,4,2), (58455,0,2), (153663,544,2), (667711,0,2), (174143,0,2), (178239,6559975,2), (60503,2017,2), (10551669,2,2), (618559,0,2), (13887,0,2), (1187887,0,2), (593983,0,2), (626751,0,2), (9634165,2243,2), (64599,0,2), (9240879,1185,2), (2785583,4801,2), (708671,803527,38), (716863,5313,2), (11338101,4,2), (665647,5185,2), (553023,5903897,2), (733247,0,2), (741439,0,2), (599799925,2,2), (190527,0,2), (194623,0,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test5_1 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket4 5 h109Block5_1 = true := by decide +kernel
def h109Block5_2 : List NodeSpec := indexTripleNodes [(11600245,2,2), (198719,1185,2), (39999,0,2), (202815,5185,2), (8716631,6209,2), (8847663,6337,2), (57887,0,2), (54335,0,2), (749631,0,2), (454743,14913,10), (227391,0,2), (503855,0,2), (251967,0,2), (11731317,2,2), (3506519,6721,2), (3899695,6977,2), (12124533,2,2), (59935,0,2), (231487,47335,2), (256063,0,2), (782399,0,2), (45352565,32,2), (3698795,497,2), (149567,0,2), (14425175,0,2), (161855,1185,2), (165951,0,2), (34645271,17537,2), (211007,0,2), (215103,0,2), (2830453,0,2), (213930091,5185,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test5_2 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket4 5 h109Block5_2 = true := by decide +kernel
def h109Block5_3 : List NodeSpec := indexPairNodes [(536639,0), (544831,5185), (3310453,9425), (12454487,1185), (247871,1185), (1031802987,0), (790591,0), (643135,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test5_3 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket4 5 h109Block5_3 = true := by decide +kernel
def h109Nodes5 : List NodeSpec := h109Block5_0 ++ h109Block5_1 ++ h109Block5_2 ++ h109Block5_3
lemma h109Check5 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket4 5 h109Nodes5 = true := by
  unfold h109Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h109Test5_0,h109Test5_1⟩,h109Test5_2⟩,h109Test5_3⟩
def h109Bucket5 : BT (List (List Nat)) := buildBucketsBT h109W h109Nodes5
set_option maxRecDepth 200000 in
lemma h109Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G 5 xs.toFinset) h109Bucket5 := buildBucketsBT_sound (by decide) h109Pairs h109WOk h109PoolsOk h109AutosOk h109Bucket4Ok h109Check5
def h109Block6_0 : List NodeSpec := indexTripleNodes [(1212,190,2), (3441013,2822,78), (4030837,45062,14), (8382,131622,10), (16574,1835558,90), (65726,955959,10), (86207,44087,10), (13887,940868102,10), (94399,1250871,10), (524478,1906201,10), (15935,66638897,46), (110783,16311577,10), (118975,1672503,10), (127167,168866023,54), (270527,7214311,10), (39999,8162518297,26), (286911,4260401,26), (42047,135376151863,26), (303295,4522727,54), (352447,3288600775,10), (50239,56962892057,10), (368831,90244711537,10), (385215,32583921,10), (54335,208348217655,10), (401599,277136071,10), (684095,38132949303,58), (5182,11403399,2), (1999679,11927687,2), (157759,262765625903,22), (4391743,27695,2), (66614,50364578,6), (56383,0x6c0c0ce184b7,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test6_0 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket5 6 h109Block6_0 = true := by decide +kernel
def h109Block6_1 : List NodeSpec := indexTripleNodes [(1475391,11680715795,2), (58431,390960039109,6), (119552063,12324103,2), (243775,5671255843127,30), (4831295,96780999,2), (219199,627168862519,6), (22108223,7967763,2), (766015,25332726407479,50), (634943,67142182,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test6_1 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket5 6 h109Block6_1 = true := by decide +kernel
def h109Nodes6 : List NodeSpec := h109Block6_0 ++ h109Block6_1
lemma h109Check6 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket5 6 h109Nodes6 = true := by
  unfold h109Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h109Test6_0,h109Test6_1⟩
def h109Bucket6 : BT (List (List Nat)) := buildBucketsBT h109W h109Nodes6
set_option maxRecDepth 200000 in
lemma h109Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G 6 xs.toFinset) h109Bucket6 := buildBucketsBT_sound (by decide) h109Pairs h109WOk h109PoolsOk h109AutosOk h109Bucket5Ok h109Check6
def h109Block7_0 : List NodeSpec := indexTripleNodes [(190,8423974,10), (574,52347576631,22), (1086,3035498365487,22), (260159,2166682136887,94), (577599,59863769399,22), (65598,122953441591,30), (12863,62012301623,30)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test7_0 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket6 7 h109Block7_0 = true := by decide +kernel
def h109Nodes7 : List NodeSpec := h109Block7_0
lemma h109Check7 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket6 7 h109Nodes7 = true := h109Test7_0
def h109Bucket7 : BT (List (List Nat)) := buildBucketsBT h109W h109Nodes7
set_option maxRecDepth 200000 in
lemma h109Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G 7 xs.toFinset) h109Bucket7 := buildBucketsBT_sound (by decide) h109Pairs h109WOk h109PoolsOk h109AutosOk h109Bucket6Ok h109Check7
def h109Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,1,8,73],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h109Test8_0 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket7 8 h109Block8_0 = true := by decide +kernel
def h109Nodes8 : List NodeSpec := h109Block8_0
lemma h109Check8 : checkNodesBT h109W h109G h109Mask h109Pools h109Autos h109Bucket7 8 h109Nodes8 = true := h109Test8_0
def h109Bucket8 : BT (List (List Nat)) := buildBucketsBT h109W h109Nodes8
set_option maxRecDepth 200000 in
lemma h109Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h109G 8 xs.toFinset) h109Bucket8 := buildBucketsBT_sound (by decide) h109Pairs h109WOk h109PoolsOk h109AutosOk h109Bucket7Ok h109Check8
set_option maxRecDepth 200000 in
lemma h109Bound : Lower h109R h109G 9 := lower_of_forestBT (essPairs := [(VAR 0,12,13),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,9,25),(VAR 5,1,33)]) (by decide +kernel) h109Bucket8Ok (by decide +kernel)
def h116R : List Nat := varsOf 61
def h116G : Nat := 0xfafafaf0faf0f0a0fafafaf0faf0f0a0
lemma h116Bound : Lower h116R h116G 9 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h109R) (T2 := h109G) (by decide +kernel) h109Bound
def h117R : List Nat := varsOf 62
def h117G : Nat := 0xfffffffcf0c0c000fffffffcf0c0c000
lemma h117Bound : Lower h117R h117G 9 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h109R) (T2 := h109G) (by decide +kernel) h109Bound
def h118R : List Nat := varsOf 62
def h118G : Nat := 0xffccffc0ffc0fc00ffccffc0ffc0fc00
lemma h118Bound : Lower h118R h118G 9 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h109R) (T2 := h109G) (by decide +kernel) h109Bound
def h119R : List Nat := varsOf 15
def h119G : Nat := 0xe888e888e888e888e888e888e888e888
lemma h119Bound : Lower h119R h119G 5 := carry_of (swaps := [(4,5),(3,4)]) (roots2 := h100R) (T2 := h100G) (by decide +kernel) h100Bound
def h120R : List Nat := varsOf 26
def h120G : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
lemma h120Bound : Lower h120R h120G 4 := carry_of (swaps := [(4,5),(1,2)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h121R : List Nat := varsOf 30
def h121G : Nat := 0xf0c0c000f0c0c000f0c0c000f0c0c000
lemma h121Bound : Lower h121R h121G 5 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h111R) (T2 := h111G) (by decide +kernel) h111Bound
def h122R : List Nat := varsOf 23
def h122G : Nat := 0xfafae8e8fafae8e8fafae8e8fafae8e8
lemma h122Bound : Lower h122R h122G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(1,2),(2,3),(0,1)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h123R : List Nat := varsOf 27
def h123G : Nat := 0xffccee88ffccee88ffccee88ffccee88
lemma h123Bound : Lower h123R h123G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h125R : List Nat := varsOf 29
def h125G : Nat := 0xfaf0f0a0faf0f0a0faf0f0a0faf0f0a0
lemma h125Bound : Lower h125R h125G 6 := carry_of (swaps := [(4,5),(2,3)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h126R : List Nat := varsOf 30
def h126G : Nat := 0xffc0fc00ffc0fc00ffc0fc00ffc0fc00
lemma h126Bound : Lower h126R h126G 6 := carry_of (swaps := [(4,5),(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h124R : List Nat := varsOf 31
def h124G : Nat := 0xfac8e888fac8e888fac8e888fac8e888
def h124Pos : List Nat := [13,14,3,3,22,14,7,13,14,11,13,22,19,25,7,11,19,22,25,28,28,28,25,3,22]
def h124Neg : List Nat := [12,12,1,2,21,10,6,9,6,10,5,6,18,9,5,9,17,18,17,24,20,12,24,18,26]
def h124Mask : Nat := fullMask 25
def h124Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xc5f6cd,0x5e494),(0xcccccccccccccccccccccccccccccccc,0x183db7e,0x1821b68),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x13a4df3,0x304d53),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x7ca7a3,0x168a2a3),(0xffff0000ffff0000ffff0000ffff0000,0x17f3810,0x1df1010)]
def h124Steps : List (Nat × Nat × Nat) := [(1,0,1),(1,0,4),(1,1,4),(0,2,3),(3,4,5),(3,1,6)]
def h124W : BT Decor := buildWiresBT 4 h124Base h124Steps
def h124AutoList : List (List (Nat × Nat)) := [[],[(2,3),(0,1)]]
def h124Autos : BT (List (Nat × Nat)) := btOfList 1 h124AutoList
lemma h124Pairs : goodPairs h124G h124Pos h124Neg := goodPairs_of (by decide +kernel)
lemma h124BaseOk : ∀ x ∈ h124Base, faithful h124Pos h124Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h124WOk : btAll (fun x => faithful h124Pos h124Neg x ∧ x.1 < 2^128) h124W := buildWiresBT_faithful h124BaseOk
lemma h124AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h124G = h124G) h124Autos := btAll_ofList (autos_of (by decide +kernel))
def h124SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 1 0,5),some (subcubeFast 1 4,4),some (subcubeFast 2 0,5),some (subcubeFast 2 8,4),some (subcubeFast 16 0,5),some (subcubeFast 16 4,4),some (subcubeFast 16 8,4),some (0xaa55aa55aa55aa55aa55aa55aa55aa55,6),some (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3,6),some (0x66666666666666666666666666666666,5)]
def h124Slices : BT (Option (Nat × Nat)) := btOfList 4 h124SliceList
def h124Specs : List PoolSpec := [(2,[]),(4,[]),(10,[]),(0,[]),(9,[]),(1,[]),(6,[]),(11,[]),(3,[]),(0,[(1,0,4)]),(8,[]),(5,[]),(2,[(0,2,3)]),(9,[(0,2,3)]),(4,[(0,2,3)]),(10,[(0,2,3)]),(6,[(0,2,3)]),(7,[])]
def h124Pools : BT (Option BoundPool) := buildPoolsBT 5 h124W h124R h124Slices h124Specs
set_option maxRecDepth 200000 in
lemma h124Slice11 : Slice h124R h124G (0x66666666666666666666666666666666) 5 := opposite_slice (oppositeRow 0 1 30) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h86Bound
set_option maxRecDepth 200000 in
lemma h124Slice10 : Slice h124R h124G (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3) 6 := mapped_slice (identifyRow 1 2 29) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h125Bound
set_option maxRecDepth 200000 in
lemma h124Slice9 : Slice h124R h124G (0xaa55aa55aa55aa55aa55aa55aa55aa55) 6 := mapped_slice (identifyRow 0 3 30) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h126Bound
set_option maxRecDepth 200000 in
lemma h124Slice8 : Slice h124R h124G (subcubeFast 16 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
lemma h124Slice7 : Slice h124R h124G (subcubeFast 16 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
lemma h124Slice6 : Slice h124R h124G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h119Bound
set_option maxRecDepth 200000 in
lemma h124Slice5 : Slice h124R h124G (subcubeFast 2 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
lemma h124Slice4 : Slice h124R h124G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h111Bound
set_option maxRecDepth 200000 in
lemma h124Slice3 : Slice h124R h124G (subcubeFast 1 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h120Bound
set_option maxRecDepth 200000 in
lemma h124Slice2 : Slice h124R h124G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h121Bound
set_option maxRecDepth 200000 in
lemma h124Slice1 : Slice h124R h124G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h122Bound
set_option maxRecDepth 200000 in
lemma h124Slice0 : Slice h124R h124G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h123Bound
lemma h124SlicesOk : btAll (sliceSpec h124R h124G) h124Slices := btAll_ofList (P := sliceSpec h124R h124G) (sliceSpecCons h124Slice0 (sliceSpecCons h124Slice1 (sliceSpecCons h124Slice2 (sliceSpecCons h124Slice3 (sliceSpecCons h124Slice4 (sliceSpecCons h124Slice5 (sliceSpecCons h124Slice6 (sliceSpecCons h124Slice7 (sliceSpecCons h124Slice8 (sliceSpecCons h124Slice9 (sliceSpecCons h124Slice10 (sliceSpecCons h124Slice11 sliceSpecNil))))))))))))
set_option maxRecDepth 200000 in
lemma h124PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h124R h124G c) h124Pools := buildPoolsBT_sound h124SlicesOk
def h124Empty : BT (List (List Nat)) := BT.empty
lemma h124EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h124G (5 - 1) xs.toFinset) h124Empty := trivial
def h124Block5_0 : List NodeSpec := indexPairNodes [(1086,0), (414,6), (2110,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h124Test5_0 : checkNodesBT h124W h124G h124Mask h124Pools h124Autos h124Empty 5 h124Block5_0 = true := by decide +kernel
def h124Nodes5 : List NodeSpec := h124Block5_0
lemma h124Check5 : checkNodesBT h124W h124G h124Mask h124Pools h124Autos h124Empty 5 h124Nodes5 = true := h124Test5_0
def h124Bucket5 : BT (List (List Nat)) := buildBucketsBT h124W h124Nodes5
set_option maxRecDepth 200000 in
lemma h124Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h124G 5 xs.toFinset) h124Bucket5 := buildBucketsBT_sound (by decide) h124Pairs h124WOk h124PoolsOk h124AutosOk h124EmptyOk h124Check5
def h124Block6_0 : List NodeSpec := indexPairNodes [(126,510), (190,4086), (574,520958)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h124Test6_0 : checkNodesBT h124W h124G h124Mask h124Pools h124Autos h124Bucket5 6 h124Block6_0 = true := by decide +kernel
def h124Nodes6 : List NodeSpec := h124Block6_0
lemma h124Check6 : checkNodesBT h124W h124G h124Mask h124Pools h124Autos h124Bucket5 6 h124Nodes6 = true := h124Test6_0
def h124Bucket6 : BT (List (List Nat)) := buildBucketsBT h124W h124Nodes6
set_option maxRecDepth 200000 in
lemma h124Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h124G 6 xs.toFinset) h124Bucket6 := buildBucketsBT_sound (by decide) h124Pairs h124WOk h124PoolsOk h124AutosOk h124Bucket5Ok h124Check6
def h124Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5,6,8,10,11,17],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h124Test7_0 : checkNodesBT h124W h124G h124Mask h124Pools h124Autos h124Bucket6 7 h124Block7_0 = true := by decide +kernel
def h124Nodes7 : List NodeSpec := h124Block7_0
lemma h124Check7 : checkNodesBT h124W h124G h124Mask h124Pools h124Autos h124Bucket6 7 h124Nodes7 = true := h124Test7_0
def h124Bucket7 : BT (List (List Nat)) := buildBucketsBT h124W h124Nodes7
set_option maxRecDepth 200000 in
lemma h124Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h124G 7 xs.toFinset) h124Bucket7 := buildBucketsBT_sound (by decide) h124Pairs h124WOk h124PoolsOk h124AutosOk h124Bucket6Ok h124Check7
set_option maxRecDepth 200000 in
lemma h124Bound : Lower h124R h124G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,6,22)]) (by decide +kernel) h124Bucket7Ok (by decide +kernel)
def h127R : List Nat := varsOf 43
def h127G : Nat := 0xee88ee8888888888ee88ee8888888888
lemma h127Bound : Lower h127R h127G 5 := carry_of (swaps := [(2,3)]) (roots2 := h100R) (T2 := h100G) (by decide +kernel) h100Bound
def h128R : List Nat := varsOf 45
def h128G : Nat := 0xaaa0aaa0a000a000aaa0aaa0a000a000
lemma h128Bound : Lower h128R h128G 5 := carry_of (swaps := [(4,5),(2,3),(0,1),(1,2),(0,1)]) (roots2 := h111R) (T2 := h111G) (by decide +kernel) h111Bound
def h129R : List Nat := varsOf 46
def h129G : Nat := 0xccc0ccc0c000c000ccc0ccc0c000c000
lemma h129Bound : Lower h129R h129G 5 := carry_of (swaps := [(4,5),(2,3),(0,1),(1,2)]) (roots2 := h111R) (T2 := h111G) (by decide +kernel) h111Bound
def h130R : List Nat := varsOf 39
def h130G : Nat := 0xeeeeeeeee8e8e8e8eeeeeeeee8e8e8e8
lemma h130Bound : Lower h130R h130G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h131R : List Nat := varsOf 43
def h131G : Nat := 0xeeeeeeeeee88ee88eeeeeeeeee88ee88
lemma h131Bound : Lower h131R h131G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(3,4),(0,1),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h132R : List Nat := varsOf 46
def h132G : Nat := 0xfffcfffcfcccfcccfffcfffcfcccfccc
lemma h132Bound : Lower h132R h132G 5 := carry_of (swaps := [(0,1)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h134R : List Nat := varsOf 45
def h134G : Nat := 0xfaf0faf0f0a0f0a0faf0faf0f0a0f0a0
lemma h134Bound : Lower h134R h134G 6 := carry_of (swaps := [(2,3)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h135R : List Nat := varsOf 46
def h135G : Nat := 0xfffcfffcc000c000fffcfffcc000c000
lemma h135Bound : Lower h135R h135G 6 := carry_of (swaps := [(3,4),(4,5),(3,4),(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h136R : List Nat := varsOf 46
def h136G : Nat := 0xffc0ffc0fc00fc00ffc0ffc0fc00fc00
lemma h136Bound : Lower h136R h136G 6 := carry_of (swaps := [(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h133R : List Nat := varsOf 47
def h133G : Nat := 0xeee8eee8e888e888eee8eee8e888e888
def h133Pos : List Nat := [13,14,3,3,14,13,14,13,38,35,37,35,37,41,41]
def h133Neg : List Nat := [12,12,1,2,10,9,6,5,6,34,5,33,33,33,9]
def h133Mask : Nat := fullMask 15
def h133Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7ead,0x7ca4),(0xcccccccccccccccccccccccccccccccc,2910,856),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5619,1475),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x60f3,0x4033),(0xffffffff00000000ffffffff00000000,0x7f00,0x3a00)]
def h133Steps : List (Nat × Nat × Nat) := []
def h133W : BT Decor := buildWiresBT 3 h133Base h133Steps
def h133AutoList : List (List (Nat × Nat)) := [[],[(3,5)],[(2,3)],[(2,5)],[(0,1)],[(3,5),(2,3)],[(3,5),(2,5)],[(3,5),(0,1)],[(2,3),(0,1)],[(2,5),(0,1)],[(3,5),(2,3),(0,1)],[(3,5),(2,5),(0,1)]]
def h133Autos : BT (List (Nat × Nat)) := btOfList 4 h133AutoList
lemma h133Pairs : goodPairs h133G h133Pos h133Neg := goodPairs_of (by decide +kernel)
lemma h133BaseOk : ∀ x ∈ h133Base, faithful h133Pos h133Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h133WOk : btAll (fun x => faithful h133Pos h133Neg x ∧ x.1 < 2^128) h133W := buildWiresBT_faithful h133BaseOk
lemma h133AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h133G = h133G) h133Autos := btAll_ofList (autos_of (by decide +kernel))
def h133SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 8,5),some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5,6),some (0xaa55aa55aa55aa55aa55aa55aa55aa55,6),some (0xaaaaaaaa55555555aaaaaaaa55555555,6),some (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3,6),some (0xcc33cc33cc33cc33cc33cc33cc33cc33,6),some (0xcccccccc33333333cccccccc33333333,6)]
def h133Slices : BT (Option (Nat × Nat)) := btOfList 4 h133SliceList
def h133Specs : List PoolSpec := [(4,[]),(0,[]),(8,[]),(9,[]),(10,[]),(5,[]),(1,[]),(11,[]),(12,[]),(13,[]),(6,[]),(2,[]),(7,[]),(3,[])]
def h133Pools : BT (Option BoundPool) := buildPoolsBT 4 h133W h133R h133Slices h133Specs
set_option maxRecDepth 200000 in
lemma h133Slice13 : Slice h133R h133G (0xcccccccc33333333cccccccc33333333) 6 := mapped_slice (identifyRow 1 5 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h112Bound
set_option maxRecDepth 200000 in
lemma h133Slice12 : Slice h133R h133G (0xcc33cc33cc33cc33cc33cc33cc33cc33) 6 := mapped_slice (identifyRow 1 3 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
lemma h133Slice11 : Slice h133R h133G (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3) 6 := mapped_slice (identifyRow 1 2 45) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h134Bound
set_option maxRecDepth 200000 in
lemma h133Slice10 : Slice h133R h133G (0xaaaaaaaa55555555aaaaaaaa55555555) 6 := mapped_slice (identifyRow 0 5 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h135Bound
set_option maxRecDepth 200000 in
lemma h133Slice9 : Slice h133R h133G (0xaa55aa55aa55aa55aa55aa55aa55aa55) 6 := mapped_slice (identifyRow 0 3 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h136Bound
set_option maxRecDepth 200000 in
lemma h133Slice8 : Slice h133R h133G (0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5) 6 := mapped_slice (identifyRow 0 2 46) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
lemma h133Slice7 : Slice h133R h133G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h100Bound
set_option maxRecDepth 200000 in
lemma h133Slice6 : Slice h133R h133G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h127Bound
set_option maxRecDepth 200000 in
lemma h133Slice5 : Slice h133R h133G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h128Bound
set_option maxRecDepth 200000 in
lemma h133Slice4 : Slice h133R h133G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h129Bound
set_option maxRecDepth 200000 in
lemma h133Slice3 : Slice h133R h133G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h130Bound
set_option maxRecDepth 200000 in
lemma h133Slice2 : Slice h133R h133G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h131Bound
set_option maxRecDepth 200000 in
lemma h133Slice1 : Slice h133R h133G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
lemma h133Slice0 : Slice h133R h133G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h132Bound
lemma h133SlicesOk : btAll (sliceSpec h133R h133G) h133Slices := btAll_ofList (P := sliceSpec h133R h133G) (sliceSpecCons h133Slice0 (sliceSpecCons h133Slice1 (sliceSpecCons h133Slice2 (sliceSpecCons h133Slice3 (sliceSpecCons h133Slice4 (sliceSpecCons h133Slice5 (sliceSpecCons h133Slice6 (sliceSpecCons h133Slice7 (sliceSpecCons h133Slice8 (sliceSpecCons h133Slice9 (sliceSpecCons h133Slice10 (sliceSpecCons h133Slice11 (sliceSpecCons h133Slice12 (sliceSpecCons h133Slice13 sliceSpecNil))))))))))))))
lemma h133PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h133R h133G c) h133Pools := buildPoolsBT_sound h133SlicesOk
def h133Empty : BT (List (List Nat)) := BT.empty
lemma h133EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h133G (7 - 1) xs.toFinset) h133Empty := trivial
def h133Block7_0 : List NodeSpec := indexPairNodes [(62,32766)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h133Test7_0 : checkNodesBT h133W h133G h133Mask h133Pools h133Autos h133Empty 7 h133Block7_0 = true := by decide +kernel
def h133Nodes7 : List NodeSpec := h133Block7_0
lemma h133Check7 : checkNodesBT h133W h133G h133Mask h133Pools h133Autos h133Empty 7 h133Nodes7 = true := h133Test7_0
def h133Bucket7 : BT (List (List Nat)) := buildBucketsBT h133W h133Nodes7
lemma h133Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h133G 7 xs.toFinset) h133Bucket7 := buildBucketsBT_sound (by decide) h133Pairs h133WOk h133PoolsOk h133AutosOk h133EmptyOk h133Check7
lemma h133Bound : Lower h133R h133G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,9,13),(VAR 3,5,13),(VAR 5,5,37)]) (by decide +kernel) h133Bucket7Ok (by decide +kernel)
def h137R : List Nat := varsOf 51
def h137G : Nat := 0xeeee888888888888eeee888888888888
lemma h137Bound : Lower h137R h137G 5 := carry_of (swaps := [(2,3),(3,4)]) (roots2 := h100R) (T2 := h100G) (by decide +kernel) h100Bound
def h138R : List Nat := varsOf 54
def h138G : Nat := 0xccccc0c0c0c00000ccccc0c0c0c00000
lemma h138Bound : Lower h138R h138G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1),(1,2)]) (roots2 := h111R) (T2 := h111G) (by decide +kernel) h111Bound
def h139R : List Nat := varsOf 23
def h139G : Nat := 0xeeeee8e8eeeee8e8eeeee8e8eeeee8e8
lemma h139Bound : Lower h139R h139G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h140R : List Nat := varsOf 51
def h140G : Nat := 0xeeeeeeeecccc8888eeeeeeeecccc8888
lemma h140Bound : Lower h140R h140G 5 := carry_of (swaps := [(2,3),(3,4)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h142R : List Nat := varsOf 53
def h142G : Nat := 0xaaaaa0a0fafaaaaaaaaaa0a0fafaaaaa
lemma h142Bound : Lower h142R h142G 6 := carry_of (swaps := [(4,5),(1,2),(2,3),(0,1)]) (roots2 := h35R) (T2 := h35G) (by decide +kernel) h35Bound
def h143R : List Nat := varsOf 53
def h143G : Nat := 0xfafaf0f0f0f0a0a0fafaf0f0f0f0a0a0
lemma h143Bound : Lower h143R h143G 6 := carry_of (swaps := [(2,3),(3,4)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h144R : List Nat := varsOf 54
def h144G : Nat := 0xfffffcfcc0c00000fffffcfcc0c00000
lemma h144Bound : Lower h144R h144G 6 := carry_of (swaps := [(3,4),(4,5),(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h141R : List Nat := varsOf 55
def h141G : Nat := 0xeeeee8e8c8c88888eeeee8e8c8c88888
def h141Pos : List Nat := [22,37,3,3,22,37,22,19,49,38,37,35,49]
def h141Neg : List Nat := [20,36,1,2,18,33,6,18,33,6,5,33,17]
def h141Mask : Nat := fullMask 13
def h141Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7598,7460),(0xcccccccccccccccccccccccccccccccc,2781,728),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1651,1603),(0xffff0000ffff0000ffff0000ffff0000,4561,4241),(0xffffffff00000000ffffffff00000000,7970,2338)]
def h141Steps : List (Nat × Nat × Nat) := []
def h141W : BT Decor := buildWiresBT 3 h141Base h141Steps
def h141AutoList : List (List (Nat × Nat)) := [[],[(2,4)]]
def h141Autos : BT (List (Nat × Nat)) := btOfList 1 h141AutoList
lemma h141Pairs : goodPairs h141G h141Pos h141Neg := goodPairs_of (by decide +kernel)
lemma h141BaseOk : ∀ x ∈ h141Base, faithful h141Pos h141Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h141WOk : btAll (fun x => faithful h141Pos h141Neg x ∧ x.1 < 2^128) h141W := buildWiresBT_faithful h141BaseOk
lemma h141AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h141G = h141G) h141Autos := btAll_ofList (autos_of (by decide +kernel))
def h141SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 2,5),some (subcubeFast 0 4,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,5),some (subcubeFast 1 0,5),some (subcubeFast 1 2,4),some (subcubeFast 4 0,5),some (subcubeFast 16 0,5),some (0xaaaaaaaa55555555aaaaaaaa55555555,6),some (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3,6),some (0xcccc3333cccc3333cccc3333cccc3333,6),some (0x33333333cccccccc33333333cccccccc,6)]
def h141Slices : BT (Option (Nat × Nat)) := btOfList 4 h141SliceList
def h141Specs : List PoolSpec := [(4,[]),(0,[]),(5,[]),(1,[]),(6,[]),(2,[]),(7,[]),(3,[]),(8,[]),(9,[]),(10,[]),(11,[])]
def h141Pools : BT (Option BoundPool) := buildPoolsBT 4 h141W h141R h141Slices h141Specs
set_option maxRecDepth 200000 in
lemma h141Slice11 : Slice h141R h141G (0x33333333cccccccc33333333cccccccc) 6 := opposite_slice (oppositeRow 1 5 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h142Bound
set_option maxRecDepth 200000 in
lemma h141Slice10 : Slice h141R h141G (0xcccc3333cccc3333cccc3333cccc3333) 6 := mapped_slice (identifyRow 1 4 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h96Bound
set_option maxRecDepth 200000 in
lemma h141Slice9 : Slice h141R h141G (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3) 6 := mapped_slice (identifyRow 1 2 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h143Bound
set_option maxRecDepth 200000 in
lemma h141Slice8 : Slice h141R h141G (0xaaaaaaaa55555555aaaaaaaa55555555) 6 := mapped_slice (identifyRow 0 5 54) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h144Bound
set_option maxRecDepth 200000 in
lemma h141Slice7 : Slice h141R h141G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h100Bound
set_option maxRecDepth 200000 in
lemma h141Slice6 : Slice h141R h141G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h137Bound
set_option maxRecDepth 200000 in
lemma h141Slice5 : Slice h141R h141G (subcubeFast 1 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
lemma h141Slice4 : Slice h141R h141G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h138Bound
set_option maxRecDepth 200000 in
lemma h141Slice3 : Slice h141R h141G (subcubeFast 0 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h139Bound
set_option maxRecDepth 200000 in
lemma h141Slice2 : Slice h141R h141G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
lemma h141Slice1 : Slice h141R h141G (subcubeFast 0 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h140Bound
set_option maxRecDepth 200000 in
lemma h141Slice0 : Slice h141R h141G (subcubeFast 0 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h55Bound
lemma h141SlicesOk : btAll (sliceSpec h141R h141G) h141Slices := btAll_ofList (P := sliceSpec h141R h141G) (sliceSpecCons h141Slice0 (sliceSpecCons h141Slice1 (sliceSpecCons h141Slice2 (sliceSpecCons h141Slice3 (sliceSpecCons h141Slice4 (sliceSpecCons h141Slice5 (sliceSpecCons h141Slice6 (sliceSpecCons h141Slice7 (sliceSpecCons h141Slice8 (sliceSpecCons h141Slice9 (sliceSpecCons h141Slice10 (sliceSpecCons h141Slice11 sliceSpecNil))))))))))))
lemma h141PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h141R h141G c) h141Pools := buildPoolsBT_sound h141SlicesOk
def h141Empty : BT (List (List Nat)) := BT.empty
lemma h141EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h141G (7 - 1) xs.toFinset) h141Empty := trivial
def h141Block7_0 : List NodeSpec := indexPairNodes [(62,8190)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h141Test7_0 : checkNodesBT h141W h141G h141Mask h141Pools h141Autos h141Empty 7 h141Block7_0 = true := by decide +kernel
def h141Nodes7 : List NodeSpec := h141Block7_0
lemma h141Check7 : checkNodesBT h141W h141G h141Mask h141Pools h141Autos h141Empty 7 h141Nodes7 = true := h141Test7_0
def h141Bucket7 : BT (List (List Nat)) := buildBucketsBT h141W h141Nodes7
lemma h141Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h141G 7 xs.toFinset) h141Bucket7 := buildBucketsBT_sound (by decide) h141Pairs h141WOk h141PoolsOk h141AutosOk h141EmptyOk h141Check7
lemma h141Bound : Lower h141R h141G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,18,22),(VAR 4,6,22),(VAR 5,5,37)]) (by decide +kernel) h141Bucket7Ok (by decide +kernel)
def h145R : List Nat := varsOf 57
def h145G : Nat := 0xaaaaaa00aa000000aaaaaa00aa000000
lemma h145Bound : Lower h145R h145G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h111R) (T2 := h111G) (by decide +kernel) h111Bound
def h146R : List Nat := varsOf 27
def h146G : Nat := 0xeeeeee88eeeeee88eeeeee88eeeeee88
lemma h146Bound : Lower h146R h146G 5 := carry_of (swaps := [(4,5),(2,3),(3,4),(0,1),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h17R) (T2 := h17G) (by decide +kernel) h17Bound
def h147R : List Nat := varsOf 51
def h147G : Nat := 0xeeeeeeeeaaaa8888eeeeeeeeaaaa8888
lemma h147Bound : Lower h147R h147G 5 := carry_of (swaps := [(2,3),(3,4),(0,1)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h148R : List Nat := varsOf 58
def h148G : Nat := 0xffffffccffccccccffffffccffcccccc
lemma h148Bound : Lower h148R h148G 5 := carry_of (swaps := [(3,4),(2,3),(0,1)]) (roots2 := h39R) (T2 := h39G) (by decide +kernel) h39Bound
def h149R : List Nat := varsOf 59
def h149G : Nat := 0xeeeeee88aa888888eeeeee88aa888888
lemma h149Bound : Lower h149R h149G 8 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h141R) (T2 := h141G) (by decide +kernel) h141Bound
def h150R : List Nat := varsOf 29
def h150G : Nat := 0xfaaaaaa0faaaaaa0faaaaaa0faaaaaa0
lemma h150Bound : Lower h150R h150G 6 := carry_of (swaps := [(4,5),(2,3),(0,1),(1,2),(0,1)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h152R : List Nat := varsOf 60
def h152G : Nat := 0xf0ff00f0f0000000f0ff00f0f0000000
lemma h152Bound : Lower h152R h152G 6 := carry_of (swaps := [(2,3)]) (roots2 := h74R) (T2 := h74G) (by decide +kernel) h74Bound
def h153R : List Nat := varsOf 57
def h153G : Nat := 0xffaaaa00ff000000ffaaaa00ff000000
lemma h153Bound : Lower h153R h153G 5 := carry_of (swaps := [(1,2),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h100R) (T2 := h100G) (by decide +kernel) h100Bound
def h154R : List Nat := varsOf 57
def h154G : Nat := 0xffaaaa00ff00aa00ffaaaa00ff00aa00
lemma h154Bound : Lower h154R h154G 5 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3)]) (roots2 := h24R) (T2 := h24G) (by decide +kernel) h24Bound
def h151R : List Nat := varsOf 61
def h151G : Nat := 0xfaaaaaa0fa00a000faaaaaa0fa00a000
def h151Pos : List Nat := [25,28,41,28,49,13,28,41,25,37,13,25,49,41,60,37,49,41,60,13,13,25,13,29,37,37,25,28,60,41,49,53,28,53,45,13,28,37,28,41,13,41,57,49,13,37,28,28,28,53,37,49]
def h151Neg : List Nat := [24,24,44,20,48,5,12,40,9,5,12,17,33,9,52,33,17,33,56,1,9,21,21,21,52,36,1,52,44,1,1,21,44,52,44,8,21,44,16,56,4,32,56,21,44,4,8,0,4,33,1,52]
def h151Mask : Nat := fullMask 52
def h151Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xe3faee7fbbfb5,0x60810e4fbbb20),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x7f17f9bdcc66a,0x939379be0466c),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1d7dd3cfe6def,0x54ad101425c7),(0xffff0000ffff0000ffff0000ffff0000,0xbcc53dca5595b,0x80cd289e5481b),(0xffffffff00000000ffffffff00000000,0xe2ea6f307f294,0xa16a71b06d094)]
def h151Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(3,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,4),(2,0,4),(3,0,4),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(2,0,19),(0,2,3),(1,2,3),(2,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(2,2,5),(3,3,4),(1,3,5),(0,0,30),(2,0,30),(0,2,30),(0,4,30),(2,4,33),(2,19,30),(2,30,33),(1,3,19),(2,3,19),(2,3,5),(1,5,19),(0,0,41),(0,2,41),(0,1,3),(1,1,3),(2,1,3),(0,1,4),(3,1,4),(0,0,22),(3,1,22),(3,5,22),(1,1,23),(3,3,52),(1,5,23),(2,0,24),(1,1,24),(1,5,24),(0,0,57),(2,0,27),(1,1,27),(0,0,60),(1,5,27),(1,1,29),(1,5,29),(1,1,33),(0,2,6),(1,1,66),(0,4,66),(2,4,66),(3,2,6),(0,3,6),(3,3,6),(0,4,6),(2,6,24),(2,6,27),(1,1,70),(1,1,73),(1,7,19),(2,4,8),(1,8,24),(1,8,27),(0,2,45),(1,3,82),(1,9,13),(1,13,82),(3,2,45),(3,9,45),(1,13,45),(3,13,45),(1,4,82),(2,4,82),(0,4,45),(0,1,10),(0,4,10),(3,11,45),(2,4,12),(0,0,38),(0,2,38),(3,3,77),(0,0,85),(0,2,85),(2,0,53),(3,14,17),(3,1,103),(1,14,19),(1,14,45),(3,14,45),(1,3,104),(1,14,82),(2,4,16),(3,16,45),(3,23,45),(2,3,18),(1,19,23),(1,19,46),(1,24,44),(3,24,45),(1,27,44),(3,27,45),(1,3,92),(1,24,46),(1,27,46),(2,0,48),(1,3,48),(0,0,124)]
def h151W : BT Decor := buildWiresBT 7 h151Base h151Steps
def h151AutoList : List (List (Nat × Nat)) := [[],[(2,4)]]
def h151Autos : BT (List (Nat × Nat)) := btOfList 1 h151AutoList
lemma h151Pairs : goodPairs h151G h151Pos h151Neg := goodPairs_of (by decide +kernel)
lemma h151BaseOk : ∀ x ∈ h151Base, faithful h151Pos h151Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h151WOk : btAll (fun x => faithful h151Pos h151Neg x ∧ x.1 < 2^128) h151W := buildWiresBT_faithful h151BaseOk
lemma h151AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h151G = h151G) h151Autos := btAll_ofList (autos_of (by decide +kernel))
def h151SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,5),some (subcubeFast 0 4,4),some (subcubeFast 0 8,5),some (subcubeFast 0 16,4),some (subcubeFast 0 32,6),some (subcubeFast 4 0,5),some (subcubeFast 4 1,4),some (subcubeFast 16 0,5),some (subcubeFast 16 1,4),some (subcubeFast 32 0,5),some (subcubeFast 32 8,4),some (0xaaaaaaaa55555555aaaaaaaa55555555,6),some (0xf00ff00ff00ff00ff00ff00ff00ff00f,5),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,5),some (0xff0000ffff0000ffff0000ffff0000ff,5),some (0x55aa55aa55aa55aa55aa55aa55aa55aa,6)]
def h151Slices : BT (Option (Nat × Nat)) := btOfList 4 h151SliceList
def h151Specs : List PoolSpec := poolSteps h151Steps [(0,[]),(5,[]),(6,[]),(4,[0]),(1,[]),(2,[]),(0,[25]),(7,[0]),(13,[]),(9,[14]),(8,[]),(3,[]),(7,[]),(14,[]),(9,[]),(4,[]),(12,[]),(4,[0,23]),(4,[0,25]),(0,[35]),(4,[0,35]),(4,[1]),(5,[61]),(5,[66]),(11,[]),(4,[1,61]),(4,[1,65]),(5,[65]),(4,[1,66]),(4,[1,67]),(5,[67]),(5,[68]),(4,[2]),(7,[2]),(15,[]),(5,[27]),(4,[3]),(2,[8]),(10,[]),(15,[8]),(9,[4]),(4,[4]),(5,[8]),(7,[8]),(2,[9]),(5,[9]),(7,[9]),(4,[54]),(5,[4]),(4,[5]),(4,[5,88]),(4,[6]),(4,[50]),(9,[7]),(4,[7]),(2,[91]),(4,[14]),(7,[8,0]),(0,[40]),(4,[40]),(5,[8,26]),(4,[12]),(4,[11]),(9,[11]),(4,[16]),(4,[18,47]),(4,[18]),(2,[105]),(5,[37]),(4,[13]),(4,[13,108]),(5,[15]),(0,[41]),(4,[14,33]),(4,[39]),(4,[39,40]),(5,[26]),(4,[41]),(4,[118]),(5,[118]),(4,[119]),(2,[50]),(4,[51]),(2,[51]),(4,[55])]
def h151Pools : BT (Option BoundPool) := buildPoolsBT 7 h151W h151R h151Slices h151Specs
set_option maxRecDepth 200000 in
lemma h151Slice15 : Slice h151R h151G (0x55aa55aa55aa55aa55aa55aa55aa55aa) 6 := opposite_slice (oppositeRow 0 3 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h152Bound
set_option maxRecDepth 200000 in
lemma h151Slice14 : Slice h151R h151G (0xff0000ffff0000ffff0000ffff0000ff) 5 := mapped_slice (identifyRow 3 4 53) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h103Bound
set_option maxRecDepth 200000 in
lemma h151Slice13 : Slice h151R h151G (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f) 5 := mapped_slice (identifyRow 2 4 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h153Bound
set_option maxRecDepth 200000 in
lemma h151Slice12 : Slice h151R h151G (0xf00ff00ff00ff00ff00ff00ff00ff00f) 5 := mapped_slice (identifyRow 2 3 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h154Bound
set_option maxRecDepth 200000 in
lemma h151Slice11 : Slice h151R h151G (0xaaaaaaaa55555555aaaaaaaa55555555) 6 := mapped_slice (identifyRow 0 5 60) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h114Bound
set_option maxRecDepth 200000 in
lemma h151Slice10 : Slice h151R h151G (subcubeFast 32 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
lemma h151Slice9 : Slice h151R h151G (subcubeFast 32 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h111Bound
set_option maxRecDepth 200000 in
lemma h151Slice8 : Slice h151R h151G (subcubeFast 16 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h151Slice7 : Slice h151R h151G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h128Bound
set_option maxRecDepth 200000 in
lemma h151Slice6 : Slice h151R h151G (subcubeFast 4 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
lemma h151Slice5 : Slice h151R h151G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h145Bound
set_option maxRecDepth 200000 in
lemma h151Slice4 : Slice h151R h151G (subcubeFast 0 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h150Bound
set_option maxRecDepth 200000 in
lemma h151Slice3 : Slice h151R h151G (subcubeFast 0 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
lemma h151Slice2 : Slice h151R h151G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h60Bound
set_option maxRecDepth 200000 in
lemma h151Slice1 : Slice h151R h151G (subcubeFast 0 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h78Bound
set_option maxRecDepth 200000 in
lemma h151Slice0 : Slice h151R h151G (subcubeFast 0 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h89Bound
lemma h151SlicesOk : btAll (sliceSpec h151R h151G) h151Slices := btAll_ofList (P := sliceSpec h151R h151G) (sliceSpecCons h151Slice0 (sliceSpecCons h151Slice1 (sliceSpecCons h151Slice2 (sliceSpecCons h151Slice3 (sliceSpecCons h151Slice4 (sliceSpecCons h151Slice5 (sliceSpecCons h151Slice6 (sliceSpecCons h151Slice7 (sliceSpecCons h151Slice8 (sliceSpecCons h151Slice9 (sliceSpecCons h151Slice10 (sliceSpecCons h151Slice11 (sliceSpecCons h151Slice12 (sliceSpecCons h151Slice13 (sliceSpecCons h151Slice14 (sliceSpecCons h151Slice15 sliceSpecNil))))))))))))))))
set_option maxRecDepth 200000 in
lemma h151PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h151R h151G c) h151Pools := buildPoolsBT_sound h151SlicesOk
def h151Empty : BT (List (List Nat)) := BT.empty
lemma h151EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h151G (4 - 1) xs.toFinset) h151Empty := trivial
def h151Block4_0 : List NodeSpec := indexPairNodes [(30293011,0), (126762003,0), (128012363,0), (366863,0), (1166035493,0), (78121525,0), (26297629,7489), (6241453341,7489), (337951,1057), (92801559,0), (24773775,0), (436255,0), (4932640843,0), (4932657227,0), (1116783849491,0), (489785733139,0), (390157323,0), (310505525,0), (487080101,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test4_0 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Empty 4 h151Block4_0 = true := by decide +kernel
def h151Nodes4 : List NodeSpec := h151Block4_0
lemma h151Check4 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Empty 4 h151Nodes4 = true := h151Test4_0
def h151Bucket4 : BT (List (List Nat)) := buildBucketsBT h151W h151Nodes4
set_option maxRecDepth 200000 in
lemma h151Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h151G 4 xs.toFinset) h151Bucket4 := buildBucketsBT_sound (by decide) h151Pairs h151WOk h151PoolsOk h151AutosOk h151EmptyOk h151Check4
def h151Block5_0 : List NodeSpec := indexPairNodes [(6060107,908), (3030123,768), (11811947,0), (729333,64), (745707,401), (194623,4), (778475,401), (206911,4), (3426351,0), (34621487,0), (219199,0), (909547,0), (948271,4), (14186543,0), (239679,0), (958699,401), (247871,4), (960559,528644), (3975215,516), (2402351,0), (60479,15493), (178276439,107553), (199247919,39961), (203442223,0), (577599,995), (165705815,0), (186677295,0), (190871599,0), (585791,995), (2871383,53345), (3919959,0), (12714603,497)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test5_0 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket4 5 h151Block5_0 = true := by decide +kernel
def h151Block5_1 : List NodeSpec := indexTripleNodes [(626751,1057,2), (634943,1057,2), (136324405,11239565,2), (11929375,6209,2), (2950773,2120,2), (38536791,7523,2), (684095,0,2), (10880799,6849,2), (37490263,0,2), (749631,1009,2), (222464555,213825,2), (3343647,0,2), (3081503,10115,2), (4852277,1945762990157,6), (973736501,965643,2), (34896874027,241905,2), (36439327,418211,2), (39585055,369123,2), (40109343,995,2), (45352223,0,2), (9702517,3469,2), (700479,1633,2), (10356511,0,2), (46925599,8001,2), (222400043,42689,2), (3213087,0,2), (2950943,0,2), (47974175,0,2), (47449887,6081,2), (35915551,1057,2), (48498463,0,2), (49022751,7745,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test5_1 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket4 5 h151Block5_1 = true := by decide +kernel
def h151Block5_2 : List NodeSpec := indexPairNodes [(822495307,68), (755910731,4), (2231447659,4), (51913835,0), (643135,1009), (38282347,17025), (806975,4), (3292267,260), (755136587,68), (202390635,4), (766015,4), (220237899,32), (207679563,4), (4664221771,3310229), (2517246027,35390053), (2785681483,516), (3188334667,19585), (52498539,32), (921663,0), (938047,0), (245385303,1057), (929855,0), (232814679,1057), (946239,497), (35715103,497), (39909407,1057), (195056671,0), (962623,0), (60903531,0), (970815,0), (616585303,4100), (608200791,4)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test5_2 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket4 5 h151Block5_2 = true := by decide +kernel
def h151Block5_3 : List NodeSpec := indexPairNodes [(995391,4), (223295,5521), (235583,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test5_3 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket4 5 h151Block5_3 = true := by decide +kernel
def h151Nodes5 : List NodeSpec := h151Block5_0 ++ h151Block5_1 ++ h151Block5_2 ++ h151Block5_3
lemma h151Check5 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket4 5 h151Nodes5 = true := by
  unfold h151Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h151Test5_0,h151Test5_1⟩,h151Test5_2⟩,h151Test5_3⟩
def h151Bucket5 : BT (List (List Nat)) := buildBucketsBT h151W h151Nodes5
set_option maxRecDepth 200000 in
lemma h151Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h151G 5 xs.toFinset) h151Bucket5 := buildBucketsBT_sound (by decide) h151Pairs h151WOk h151PoolsOk h151AutosOk h151Bucket4Ok h151Check5
def h151Block6_0 : List NodeSpec := indexPairNodes [(59627,1390), (71807,12358), (75903,30724), (79999,3461), (92287,98372), (50239,520206), (100479,45060), (108591,529036), (54335,646126), (299055,509205), (303295,5000311), (352447,5000243), (512087,75630634), (256063,75757614), (1089623,12717203), (1105967,93193235), (1122351,13244947), (288799,4332816418), (205675,6423727), (127423,108), (270783,161836), (287167,32808), (336319,98412), (369087,32812), (58431,1695500717), (1081663,313031), (1278271,5000243), (161855,64711), (313375,1679331527), (17436,2107687179), (17438,16831889675), (33822,67440361739)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test6_0 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket5 6 h151Block6_0 = true := by decide +kernel
def h151Block6_1 : List NodeSpec := indexTripleNodes [(344895,2820752327,2), (4784959,620915887,2), (260159,8630382,2), (1466475,21236775,2), (1220715,2154,2), (374815,6846716107,2), (36894,12069159179,2), (4523839,14444,2), (593983,96908463,2), (24604,1043792139,2), (383007,67115303179,2), (214303,465089082251,2), (8520991,2167647781131,6), (33817887,216503851275,2), (17040959,373382703,2), (602175,554088771690,2), (5407,27032437003,2), (59167,2088438539,2), (182047,1417349899,2), (4130591,122664567051,6), (15475819,1491614037,2), (365119,45236893765,6), (496191,15307664261,2), (15935,1359393967,2), (651327,249934,6), (440351,47816182037,2), (157759,262102496431,6), (202815,94497399,6), (1777711,7214293,2), (888895,49343087,2), (1794095,30678229,2), (33855,644287476911,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test6_1 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket5 6 h151Block6_1 = true := by decide +kernel
def h151Block6_2 : List NodeSpec := indexTripleNodes [(32319,58203255,2), (13909099,390170965,6), (14433387,507611477,2), (302655,60293,2), (141375,964930167,6), (5119551,139364,2), (5381695,143460,2), (133183,77721107,2), (1712203,9404941397,2), (21505087,40964,6), (18365503,98372,2), (905279,106574,2), (56383,730203519919,6), (7625791,79517750063,2), (22553663,98400,2), (19414079,110692,2), (643135,77724279,2), (314611775,1459696869,2), (348166207,12388,2), (398497855,1458673,2), (23602239,45060,2), (20462655,98372,2), (774207,249934,2), (170047,3573986479,2), (954431,46202464879,2), (979007,897711256751,2), (987199,182567676535,6), (211007,8115909122679,2), (215103,932062648951,2), (227391,272718455,2), (231487,1166105207,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test6_2 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket5 6 h151Block6_2 = true := by decide +kernel
def h151Nodes6 : List NodeSpec := h151Block6_0 ++ h151Block6_1 ++ h151Block6_2
lemma h151Check6 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket5 6 h151Nodes6 = true := by
  unfold h151Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h151Test6_0,h151Test6_1⟩,h151Test6_2⟩
def h151Bucket6 : BT (List (List Nat)) := buildBucketsBT h151W h151Nodes6
set_option maxRecDepth 200000 in
lemma h151Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h151G 6 xs.toFinset) h151Bucket6 := buildBucketsBT_sound (by decide) h151Pairs h151WOk h151PoolsOk h151AutosOk h151Bucket5Ok h151Check6
def h151Block7_0 : List NodeSpec := indexTripleNodes [(126,108638,2), (190,37857390,2), (318,5419715759,2), (574,26869386279,2), (1086,121391883887,6), (2110,54773753455,6), (4158,1856558671471,6), (8254,0x8408a0c5266f,2), (5407,197280011,6), (9791,15582176879,6), (5919,67594,6), (65598,7791126127,2), (12863,26322447983,2), (13887,50497412271,6), (14911,33838640751,2), (15935,2543178701999,6), (165951,249605743,2), (170047,1493527727,6), (174143,524376687,2), (178239,1947774575,2), (182335,3895549103,6), (42047,3895548967,6), (48191,33660998,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test7_0 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket6 7 h151Block7_0 = true := by decide +kernel
def h151Nodes7 : List NodeSpec := h151Block7_0
lemma h151Check7 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket6 7 h151Nodes7 = true := h151Test7_0
def h151Bucket7 : BT (List (List Nat)) := buildBucketsBT h151W h151Nodes7
set_option maxRecDepth 200000 in
lemma h151Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h151G 7 xs.toFinset) h151Bucket7 := buildBucketsBT_sound (by decide) h151Pairs h151WOk h151PoolsOk h151AutosOk h151Bucket6Ok h151Check7
def h151Block8_0 : List NodeSpec := [([0,1,2,3,4],[15],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h151Test8_0 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket7 8 h151Block8_0 = true := by decide +kernel
def h151Nodes8 : List NodeSpec := h151Block8_0
lemma h151Check8 : checkNodesBT h151W h151G h151Mask h151Pools h151Autos h151Bucket7 8 h151Nodes8 = true := h151Test8_0
def h151Bucket8 : BT (List (List Nat)) := buildBucketsBT h151W h151Nodes8
set_option maxRecDepth 200000 in
lemma h151Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h151G 8 xs.toFinset) h151Bucket8 := buildBucketsBT_sound (by decide) h151Pairs h151WOk h151PoolsOk h151AutosOk h151Bucket7Ok h151Check8
set_option maxRecDepth 200000 in
lemma h151Bound : Lower h151R h151G 9 := lower_of_forestBT (essPairs := [(VAR 0,12,13),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,9,25),(VAR 5,5,37)]) (by decide +kernel) h151Bucket8Ok (by decide +kernel)
def h155R : List Nat := varsOf 30
def h155G : Nat := 0xfcccccc0fcccccc0fcccccc0fcccccc0
lemma h155Bound : Lower h155R h155G 6 := carry_of (swaps := [(4,5),(2,3),(0,1),(1,2)]) (roots2 := h18R) (T2 := h18G) (by decide +kernel) h18Bound
def h156R : List Nat := varsOf 46
def h156G : Nat := 0xfcccfcccf0c0f0c0fcccfcccf0c0f0c0
lemma h156Bound : Lower h156R h156G 4 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h46R) (T2 := h46G) (by decide +kernel) h46Bound
def h157R : List Nat := varsOf 58
def h157G : Nat := 0xffccccccffcccc00ffccccccffcccc00
lemma h157Bound : Lower h157R h157G 5 := carry_of (swaps := [(2,3),(3,4),(4,5),(0,1),(1,2),(2,3),(0,1)]) (roots2 := h14R) (T2 := h14G) (by decide +kernel) h14Bound
def h158R : List Nat := varsOf 62
def h158G : Nat := 0xfcccccc0f0c0c000fcccccc0f0c0c000
lemma h158Bound : Lower h158R h158G 9 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h151R) (T2 := h151G) (by decide +kernel) h151Bound
def h160R : List Nat := varsOf 30
def h160G : Nat := 0xfcccfffcfcccfffcfcccfffcfcccfffc
lemma h160Bound : Lower h160R h160G 5 := carry_of (swaps := [(0,1)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h161R : List Nat := varsOf 30
def h161G : Nat := 0xfcffccfcfcffccfcfcffccfcfcffccfc
lemma h161Bound : Lower h161R h161G 5 := carry_of (swaps := [(3,4),(0,1)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h162R : List Nat := varsOf 30
def h162G : Nat := 0xffcfcfccffcfcfccffcfcfccffcfcfcc
lemma h162Bound : Lower h162R h162G 5 := carry_of (swaps := [(3,4),(2,3),(0,1)]) (roots2 := h45R) (T2 := h45G) (by decide +kernel) h45Bound
def h163R : List Nat := varsOf 27
def h163G : Nat := 0xffeeee88ffeeee88ffeeee88ffeeee88
lemma h163Bound : Lower h163R h163G 7 := carry_of (swaps := [(3,4),(4,5),(1,2)]) (roots2 := h49R) (T2 := h49G) (by decide +kernel) h49Bound
def h159R : List Nat := varsOf 31
def h159G : Nat := 0xfeeeeee8feeeeee8feeeeee8feeeeee8
def h159Pos : List Nat := [5,6,3,3,6,5,9,17,28,28,13,10,18,9,18,28,21,9,3,17,10,14,5,14,22,5,7,18,6,11,11,17]
def h159Neg : List Nat := [4,4,1,2,2,1,1,1,12,20,12,2,2,8,20,24,20,12,4,20,8,2,12,12,20,0,4,16,12,2,1,16]
def h159Mask : Nat := fullMask 32
def h159Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xe64f24ed,0x400000e4),(0xcccccccccccccccccccccccccccccccc,0x7db4581e,0x20201818),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x17e18733,0x15cf4703),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x60b2af40,0x10d2a500),(0xffff0000ffff0000ffff0000ffff0000,0x8909d380,0x8909c200)]
def h159Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(1,0,2),(1,1,2),(1,3,4),(1,3,8),(3,3,11),(3,4,11),(1,6,9),(3,6,9),(1,4,12),(3,4,12),(0,8,9),(0,2,3),(1,2,3),(2,2,3),(0,2,6),(3,2,6),(3,1,2),(1,1,3),(1,4,20),(2,6,20),(0,8,25),(1,6,28),(3,3,25),(3,1,8),(1,3,31),(1,3,22),(2,3,22),(1,3,23),(3,1,11),(1,12,30),(1,1,12),(3,0,2),(1,0,19),(3,1,40),(1,19,23),(2,6,19),(3,0,14),(2,14,22),(1,1,44),(1,4,21),(1,4,5),(3,5,37),(1,0,15),(3,4,35),(2,8,24),(3,0,26)]
def h159W : BT Decor := buildWiresBT 6 h159Base h159Steps
def h159AutoList : List (List (Nat × Nat)) := [[],[(3,4)],[(2,3)],[(2,4)],[(0,1)],[(3,4),(2,3)],[(3,4),(2,4)],[(3,4),(0,1)],[(2,3),(0,1)],[(2,4),(0,1)],[(3,4),(2,3),(0,1)],[(3,4),(2,4),(0,1)]]
def h159Autos : BT (List (Nat × Nat)) := btOfList 4 h159AutoList
lemma h159Pairs : goodPairs h159G h159Pos h159Neg := goodPairs_of (by decide +kernel)
lemma h159BaseOk : ∀ x ∈ h159Base, faithful h159Pos h159Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h159WOk : btAll (fun x => faithful h159Pos h159Neg x ∧ x.1 < 2^128) h159W := buildWiresBT_faithful h159BaseOk
lemma h159AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h159G = h159G) h159Autos := btAll_ofList (autos_of (by decide +kernel))
def h159SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 1 0,6),some (subcubeFast 2 0,6),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 12 0,4),some (subcubeFast 16 0,5),some (subcubeFast 20 0,4),some (subcubeFast 24 0,4),some (0xf00ff00ff00ff00ff00ff00ff00ff00f,7),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,7),some (0xff0000ffff0000ffff0000ffff0000ff,7),some (0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a,5),some (0x55aa55aa55aa55aa55aa55aa55aa55aa,5),some (0x5555aaaa5555aaaa5555aaaa5555aaaa,5),some (0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c,5),some (0x33cc33cc33cc33cc33cc33cc33cc33cc,5),some (0x3333cccc3333cccc3333cccc3333cccc,5)]
def h159Slices : BT (Option (Nat × Nat)) := btOfList 5 h159SliceList
def h159Specs : List PoolSpec := poolSteps h159Steps [(0,[]),(1,[]),(1,[3]),(2,[]),(0,[4]),(8,[1,3]),(9,[1,3]),(0,[14]),(8,[1,35]),(8,[1]),(3,[]),(5,[15]),(8,[]),(5,[]),(13,[]),(0,[15]),(9,[15]),(4,[]),(11,[]),(8,[1,22]),(9,[1]),(0,[17]),(8,[1,17]),(9,[1,17,28]),(9,[1,17]),(0,[17,29]),(9,[16]),(9,[]),(1,[10]),(0,[18]),(1,[18]),(8,[1,18]),(9,[1,18]),(10,[]),(10,[1]),(14,[]),(0,[19]),(8,[3]),(6,[]),(9,[3]),(8,[20]),(15,[]),(0,[26]),(8,[3,26]),(9,[3,26]),(16,[]),(10,[3,15]),(8,[21]),(8,[3,5]),(9,[3,5]),(10,[3]),(8,[5]),(9,[5]),(7,[]),(0,[6]),(12,[]),(8,[3,7]),(1,[34]),(8,[34]),(9,[34]),(10,[34]),(1,[14]),(8,[35,36]),(8,[35]),(9,[14,35]),(10,[14,35]),(9,[14]),(10,[14]),(1,[15]),(10,[15])]
def h159Pools : BT (Option BoundPool) := buildPoolsBT 7 h159W h159R h159Slices h159Specs
set_option maxRecDepth 200000 in
lemma h159Slice16 : Slice h159R h159G (0x3333cccc3333cccc3333cccc3333cccc) 5 := opposite_slice (oppositeRow 1 4 29) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h45Bound
set_option maxRecDepth 200000 in
lemma h159Slice15 : Slice h159R h159G (0x33cc33cc33cc33cc33cc33cc33cc33cc) 5 := opposite_slice (oppositeRow 1 3 29) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h59Bound
set_option maxRecDepth 200000 in
lemma h159Slice14 : Slice h159R h159G (0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c) 5 := opposite_slice (oppositeRow 1 2 29) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h75Bound
set_option maxRecDepth 200000 in
lemma h159Slice13 : Slice h159R h159G (0x5555aaaa5555aaaa5555aaaa5555aaaa) 5 := opposite_slice (oppositeRow 0 4 30) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h160Bound
set_option maxRecDepth 200000 in
lemma h159Slice12 : Slice h159R h159G (0x55aa55aa55aa55aa55aa55aa55aa55aa) 5 := opposite_slice (oppositeRow 0 3 30) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h161Bound
set_option maxRecDepth 200000 in
lemma h159Slice11 : Slice h159R h159G (0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a) 5 := opposite_slice (oppositeRow 0 2 30) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h162Bound
set_option maxRecDepth 200000 in
lemma h159Slice10 : Slice h159R h159G (0xff0000ffff0000ffff0000ffff0000ff) 7 := mapped_slice (identifyRow 3 4 23) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h106Bound
set_option maxRecDepth 200000 in
lemma h159Slice9 : Slice h159R h159G (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f) 7 := mapped_slice (identifyRow 2 4 27) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h163Bound
set_option maxRecDepth 200000 in
lemma h159Slice8 : Slice h159R h159G (0xf00ff00ff00ff00ff00ff00ff00ff00f) 7 := mapped_slice (identifyRow 2 3 27) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h163Bound
set_option maxRecDepth 200000 in
lemma h159Slice7 : Slice h159R h159G (subcubeFast 24 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
lemma h159Slice6 : Slice h159R h159G (subcubeFast 20 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
lemma h159Slice5 : Slice h159R h159G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
lemma h159Slice4 : Slice h159R h159G (subcubeFast 12 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h101Bound
set_option maxRecDepth 200000 in
lemma h159Slice3 : Slice h159R h159G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h139Bound
set_option maxRecDepth 200000 in
lemma h159Slice2 : Slice h159R h159G (subcubeFast 4 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h146Bound
set_option maxRecDepth 200000 in
lemma h159Slice1 : Slice h159R h159G (subcubeFast 2 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h150Bound
set_option maxRecDepth 200000 in
lemma h159Slice0 : Slice h159R h159G (subcubeFast 1 0) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h155Bound
lemma h159SlicesOk : btAll (sliceSpec h159R h159G) h159Slices := btAll_ofList (P := sliceSpec h159R h159G) (sliceSpecCons h159Slice0 (sliceSpecCons h159Slice1 (sliceSpecCons h159Slice2 (sliceSpecCons h159Slice3 (sliceSpecCons h159Slice4 (sliceSpecCons h159Slice5 (sliceSpecCons h159Slice6 (sliceSpecCons h159Slice7 (sliceSpecCons h159Slice8 (sliceSpecCons h159Slice9 (sliceSpecCons h159Slice10 (sliceSpecCons h159Slice11 (sliceSpecCons h159Slice12 (sliceSpecCons h159Slice13 (sliceSpecCons h159Slice14 (sliceSpecCons h159Slice15 (sliceSpecCons h159Slice16 sliceSpecNil)))))))))))))))))
set_option maxRecDepth 200000 in
lemma h159PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h159R h159G c) h159Pools := buildPoolsBT_sound h159SlicesOk
def h159Empty : BT (List (List Nat)) := BT.empty
lemma h159EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G (3 - 1) xs.toFinset) h159Empty := trivial
def h159Block3_0 : List NodeSpec := nodesWithIdentity [([4,6,20,28],[]),([4,6,18,37],[]),([2,6,37,48],[]),([2,4,6,49],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test3_0 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Empty 3 h159Block3_0 = true := by decide +kernel
def h159Nodes3 : List NodeSpec := h159Block3_0
lemma h159Check3 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Empty 3 h159Nodes3 = true := h159Test3_0
def h159Bucket3 : BT (List (List Nat)) := buildBucketsBT h159W h159Nodes3
set_option maxRecDepth 200000 in
lemma h159Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G 3 xs.toFinset) h159Bucket3 := buildBucketsBT_sound (by decide) h159Pairs h159WOk h159PoolsOk h159AutosOk h159EmptyOk h159Check3
def h159Block4_0 : List NodeSpec := indexPairNodes [(5296,4), (9392,0), (69206688,0), (368829,6), (19419437,0), (1121847,0), (315479,0), (4981815,913), (5114423,47281), (340055,0), (17567255,63665), (516525,0), (99359,0), (4457527,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test4_0 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket3 4 h159Block4_0 = true := by decide +kernel
def h159Nodes4 : List NodeSpec := h159Block4_0
lemma h159Check4 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket3 4 h159Nodes4 = true := h159Test4_0
def h159Bucket4 : BT (List (List Nat)) := buildBucketsBT h159W h159Nodes4
set_option maxRecDepth 200000 in
lemma h159Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G 4 xs.toFinset) h159Bucket4 := buildBucketsBT_sound (by decide) h159Pairs h159WOk h159PoolsOk h159AutosOk h159Bucket3Ok h159Check4
def h159Block5_0 : List NodeSpec := indexTripleNodes [(1712,62,294), (1720,22,2), (2294973,0,42), (3081405,6,2), (2097844,0,34), (8389300,194,2), (4068005,2,2), (4284,4,10), (8380,4,2), (2261365,516,2), (605271,0,2), (52287,1969,2), (161855,0,2), (857175,9393,2), (48191,1313,2), (8421430,10721,6), (934191,1697,2), (39999,0,2), (165951,0,2), (988247,59569,2), (274479,0,2), (137279,0,2), (2523509,803,2), (1032495,0,2), (2916725,803,2), (2235479,0,2), (64575,254177,2), (37233829,16,2), (5174,4,2), (9270,0,2), (11666007,0,2), (69206566,0,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test5_0 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket4 5 h159Block5_0 = true := by decide +kernel
def h159Block5_1 : List NodeSpec := indexPairNodes [(50239,6), (12060759,369), (58431,0), (2105894,433), (2425431,4096067), (10286,54049), (13887,0), (133183,0), (9791,0), (8508,0), (9700399,1249), (141375,1249), (12863,1825), (153663,8129), (202815,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test5_1 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket4 5 h159Block5_1 = true := by decide +kernel
def h159Nodes5 : List NodeSpec := h159Block5_0 ++ h159Block5_1
lemma h159Check5 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket4 5 h159Nodes5 = true := by
  unfold h159Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨h159Test5_0,h159Test5_1⟩
def h159Bucket5 : BT (List (List Nat)) := buildBucketsBT h159W h159Nodes5
set_option maxRecDepth 200000 in
lemma h159Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G 5 xs.toFinset) h159Bucket5 := buildBucketsBT_sound (by decide) h159Pairs h159WOk h159PoolsOk h159AutosOk h159Bucket4Ok h159Check5
def h159Block6_0 : List NodeSpec := indexTripleNodes [(700,222,6), (110783,3350,42), (118975,855062,554), (270527,902423,38), (32830,1250481,38), (32958,2622512,38), (65726,1383945,34), (39999,512512455,6), (286911,1515031,34), (1590,62,294), (1598,4594239,2), (2163287,31919391,2), (1147199,15843553,42), (56383,135841029023,6), (1540415,7967,34), (819799,10219545371,34), (2622,4257333473,6), (4158,1845895429,10), (8254,524061028807,2), (8766,5236336931,2), (174143,1376938583,2), (149567,521918394647,2), (46143,36327248826311,1594)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test6_0 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket5 6 h159Block6_0 = true := by decide +kernel
def h159Nodes6 : List NodeSpec := h159Block6_0
lemma h159Check6 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket5 6 h159Nodes6 = true := h159Test6_0
def h159Bucket6 : BT (List (List Nat)) := buildBucketsBT h159W h159Nodes6
set_option maxRecDepth 200000 in
lemma h159Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G 6 xs.toFinset) h159Bucket6 := buildBucketsBT_sound (by decide) h159Pairs h159WOk h159PoolsOk h159AutosOk h159Bucket5Ok h159Check6
def h159Block7_0 : List NodeSpec := indexTripleNodes [(190,244215063,1598), (574,3175329481503,6), (145471,0x79c1c2825717,34), (15935,0xd8f071a2b117,34), (33855,0xfa0e1479717,1594)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test7_0 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket6 7 h159Block7_0 = true := by decide +kernel
def h159Nodes7 : List NodeSpec := h159Block7_0
lemma h159Check7 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket6 7 h159Nodes7 = true := h159Test7_0
def h159Bucket7 : BT (List (List Nat)) := buildBucketsBT h159W h159Nodes7
set_option maxRecDepth 200000 in
lemma h159Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G 7 xs.toFinset) h159Bucket7 := buildBucketsBT_sound (by decide) h159Pairs h159WOk h159PoolsOk h159AutosOk h159Bucket6Ok h159Check7
def h159Block8_0 : List NodeSpec := [([0,1,2,3,4],[0,1,12,27,33],[0,1,2,3,4,8,9])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h159Test8_0 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket7 8 h159Block8_0 = true := by decide +kernel
def h159Nodes8 : List NodeSpec := h159Block8_0
lemma h159Check8 : checkNodesBT h159W h159G h159Mask h159Pools h159Autos h159Bucket7 8 h159Nodes8 = true := h159Test8_0
def h159Bucket8 : BT (List (List Nat)) := buildBucketsBT h159W h159Nodes8
set_option maxRecDepth 200000 in
lemma h159Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h159G 8 xs.toFinset) h159Bucket8 := buildBucketsBT_sound (by decide) h159Pairs h159WOk h159PoolsOk h159AutosOk h159Bucket7Ok h159Check8
set_option maxRecDepth 200000 in
lemma h159Bound : Lower h159R h159G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9),(VAR 4,1,17)]) (by decide +kernel) h159Bucket8Ok (by decide +kernel)
def h164R : List Nat := varsOf 47
def h164G : Nat := 0xfeeefeeefac8fac8feeefeeefac8fac8
lemma h164Bound : Lower h164R h164G 6 := lift_of (z := 12) (o := 0) (essPairs := [(VAR 2,2,6),(VAR 3,1,9)]) (by decide +kernel) h15Bound
def h166R : List Nat := varsOf 39
def h166G : Nat := 0xfefefefee8e8e8e8fefefefee8e8e8e8
lemma h166Bound : Lower h166R h166G 7 := carry_of (swaps := [(3,4),(1,2),(2,3)]) (roots2 := h49R) (T2 := h49G) (by decide +kernel) h49Bound
def h165R : List Nat := varsOf 55
def h165G : Nat := 0xfefeeeeefafae8e8fefeeeeefafae8e8
def h165Pos : List Nat := [5,6,3,3,6,5,20,17,17,34,33,33,50,20,52,50,52]
def h165Neg : List Nat := [4,4,1,2,2,1,4,1,16,2,1,32,48,16,48,18,36]
def h165Mask : Nat := fullMask 17
def h165Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3501,1188),(0xcccccccccccccccccccccccccccccccc,0x921e,0x8218),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x16073,0x10043),(0xffff0000ffff0000ffff0000ffff0000,0x1f1c0,0xf100),(0xffffffff00000000ffffffff00000000,0x1de00,0x15800)]
def h165Steps : List (Nat × Nat × Nat) := []
def h165W : BT Decor := buildWiresBT 3 h165Base h165Steps
def h165AutoList : List (List (Nat × Nat)) := [[],[(4,5),(1,2)]]
def h165Autos : BT (List (Nat × Nat)) := btOfList 1 h165AutoList
lemma h165Pairs : goodPairs h165G h165Pos h165Neg := goodPairs_of (by decide +kernel)
lemma h165BaseOk : ∀ x ∈ h165Base, faithful h165Pos h165Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
lemma h165WOk : btAll (fun x => faithful h165Pos h165Neg x ∧ x.1 < 2^128) h165W := buildWiresBT_faithful h165BaseOk
lemma h165AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h165G = h165G) h165Autos := btAll_ofList (autos_of (by decide +kernel))
def h165SliceList : List (Option (Nat × Nat)) := [some (0xffff00000000ffffffff00000000ffff,7)]
def h165Slices : BT (Option (Nat × Nat)) := btOfList 1 h165SliceList
def h165Specs : List PoolSpec := [(0,[])]
def h165Pools : BT (Option BoundPool) := buildPoolsBT 1 h165W h165R h165Slices h165Specs
set_option maxRecDepth 200000 in
lemma h165Slice0 : Slice h165R h165G (0xffff00000000ffffffff00000000ffff) 7 := mapped_slice (identifyRow 4 5 39) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h166Bound
lemma h165SlicesOk : btAll (sliceSpec h165R h165G) h165Slices := btAll_ofList (P := sliceSpec h165R h165G) (sliceSpecCons h165Slice0 sliceSpecNil)
lemma h165PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h165R h165G c) h165Pools := buildPoolsBT_sound h165SlicesOk
def h165Empty : BT (List (List Nat)) := BT.empty
lemma h165EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h165G (6 - 1) xs.toFinset) h165Empty := trivial
def h165Block6_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h165Test6_0 : checkNodesBT h165W h165G h165Mask h165Pools h165Autos h165Empty 6 h165Block6_0 = true := by decide +kernel
def h165Nodes6 : List NodeSpec := h165Block6_0
lemma h165Check6 : checkNodesBT h165W h165G h165Mask h165Pools h165Autos h165Empty 6 h165Nodes6 = true := h165Test6_0
def h165Bucket6 : BT (List (List Nat)) := buildBucketsBT h165W h165Nodes6
lemma h165Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h165G 6 xs.toFinset) h165Bucket6 := buildBucketsBT_sound (by decide) h165Pairs h165WOk h165PoolsOk h165AutosOk h165EmptyOk h165Check6
lemma h165Bound : Lower h165R h165G 7 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 4,1,17),(VAR 5,1,33)]) (by decide +kernel) h165Bucket6Ok (by decide +kernel)
def h167R : List Nat := varsOf 59
def h167G : Nat := 0xffeeeeeeffccee88ffeeeeeeffccee88
lemma h167Bound : Lower h167R h167G 7 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h165R) (T2 := h165G) (by decide +kernel) h165Bound
def h168R : List Nat := varsOf 61
def h168G : Nat := 0xfffffffafafafaaafffffffafafafaaa
lemma h168Bound : Lower h168R h168G 6 := lift_of (z := 9) (o := 0) (essPairs := [(VAR 0,0,1),(VAR 3,4,12)]) (by decide +kernel) h54Bound
def h169R : List Nat := varsOf 62
def h169G : Nat := 0xfffffffcffccfcccfffffffcffccfccc
lemma h169Bound : Lower h169R h169G 6 := carry_of (swaps := [(2,3),(0,1)]) (roots2 := h168R) (T2 := h168G) (by decide +kernel) h168Bound
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfeeeeee8fac8e888feeeeee8fac8e888
def h0Pos : List Nat := [13,14,3,3,22,14,7,13,14,11,13,22,19,25,38,35,37,7,11,19,35,22,25,37,42,41,41,28,49,49,28,45,22,28,60,53,28,60,49,50,49,60,37,28,30,29,27,23,50,38,13,37,25,14,49,53,37,28,41,42,22,13,28,58,41,41,22,28,25,60,13,38,46,54,14,28,37,25,42,50,49,42,57,25,13,3,58,11,3,19,35,50,42,14,3,11,38,3,25,22,29,11,30,35,53,57,53,3,54]
def h0Neg : List Nat := [12,12,1,2,21,10,6,9,6,10,5,6,18,9,6,34,5,5,9,17,33,18,17,33,34,9,44,21,17,33,12,44,26,24,56,21,44,52,48,48,1,44,21,20,26,21,26,21,34,36,1,36,26,26,52,52,52,52,1,40,20,21,4,26,33,40,2,8,1,40,44,34,44,52,44,56,1,24,26,26,21,44,56,56,8,9,56,1,17,1,1,18,10,8,10,2,52,18,8,4,9,26,6,2,33,33,5,0,34]
def h0Mask : Nat := fullMask 109
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfb6c7bd305325dce548b6dfb6cd,0x71007a110112404a5083adf2494),(0xcccccccccccccccccccccccccccccccc,0x18ebffe2c7849823d081013edb7e,0x10e2d800c084803150010120db68),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x155920101fec73aebe3fc8a34df3,0x4490003074073caae38cc034d53),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x274b0de6d7bee347a36cf4427a3,0x34707eed6a88305217c60422a3),(0xffff0000ffff0000ffff0000ffff0000,0x175c0a4daa3cd2d1fbff78683810,0x23094dea00b3f0fcef18681010),(0xffffffff00000000ffffffff00000000,0x17811c47d3a38dcb07ecb791c000,0x1301004e0fe30bcb02f4a5908000)]
def h0Steps : List (Nat × Nat × Nat) := [(1,0,1),(2,0,1),(3,0,1),(1,0,2),(3,0,2),(1,0,3),(3,0,3),(1,0,4),(3,0,4),(3,0,5),(1,1,2),(3,1,2),(1,1,3),(3,1,3),(1,1,4),(3,1,4),(3,1,5),(0,2,3),(1,0,23),(3,1,24),(1,2,3),(2,2,3),(3,2,3),(0,2,4),(1,2,4),(2,2,4),(3,2,4),(0,2,5),(3,2,5),(0,2,6),(3,2,6),(0,3,4),(1,3,4),(2,3,4),(3,3,4),(0,3,5),(2,3,5),(3,3,5),(0,3,6),(3,3,6),(0,4,5),(1,4,5),(3,4,5),(0,4,6),(3,4,6),(0,5,6),(3,5,6),(3,3,36),(1,4,23),(1,4,36),(3,4,36),(2,5,23),(1,0,46),(1,2,46),(0,5,59),(2,6,23),(1,3,46),(3,46,61),(2,6,46),(1,23,46),(1,0,48),(1,1,48),(1,2,48),(1,3,48),(2,6,48),(1,23,48),(0,3,54),(1,2,51),(1,3,51),(1,4,51),(1,51,54),(1,23,51),(3,4,76),(2,6,57),(3,0,26),(1,2,49),(0,4,26),(1,4,26),(3,4,26),(1,2,84),(1,3,84),(0,6,84),(2,6,84),(0,5,26),(0,6,26),(1,3,90),(1,4,90),(1,49,90),(2,26,49),(1,26,52),(2,26,52),(1,4,53),(1,50,53),(1,0,82),(1,2,82),(1,3,82),(3,3,83),(0,52,93),(3,52,83),(1,0,27),(1,1,27),(1,4,27),(2,6,27),(1,0,29),(3,1,109),(1,1,41),(1,2,41),(1,4,41),(2,6,41),(1,1,43),(1,2,43),(1,4,43),(1,1,29),(2,6,29),(3,41,119),(1,29,41),(1,29,43),(3,0,30),(3,1,30),(3,1,38),(0,6,30),(1,1,39),(1,2,102),(2,6,102),(1,4,44),(2,30,44),(1,4,126),(1,30,52),(2,30,52),(1,45,56),(1,0,72),(1,1,72),(1,0,31),(1,1,31),(2,6,31),(1,31,41),(1,31,43),(0,6,68),(1,0,32),(1,1,32),(1,3,32),(2,6,32),(1,0,33),(3,1,148),(1,1,33),(3,0,150),(1,3,33),(3,4,152),(1,4,33),(2,6,33),(1,0,34),(1,1,34),(1,3,34),(3,4,158),(0,6,158),(1,4,34),(2,6,34),(1,34,44),(0,6,161),(2,6,161),(1,34,49),(1,4,162),(3,4,91),(1,35,48),(1,51,132),(0,6,47),(3,4,73),(3,35,74),(3,1,58),(3,1,9),(3,3,9),(3,4,9),(3,4,16),(1,4,17),(2,9,17),(0,9,38),(2,9,43),(2,9,48),(3,4,18),(0,9,184),(0,9,18),(1,4,186),(0,5,186),(2,5,186),(2,9,31),(2,9,19),(3,2,20),(0,9,20),(1,4,176),(1,2,21),(2,9,21),(1,2,22),(1,3,22),(1,0,124),(3,0,139),(1,0,37),(2,9,37),(0,9,127),(2,9,39),(2,9,40),(2,9,41),(2,9,46),(1,1,10),(1,3,10),(1,4,10),(3,10,16),(3,10,38),(1,10,19),(3,10,20),(1,10,21),(3,10,30),(1,10,37),(1,10,39),(3,4,218),(1,10,40),(1,10,41),(1,10,43),(1,10,46),(1,10,48),(3,1,11),(3,2,11),(3,4,11),(0,11,16),(2,11,17),(0,11,20),(2,11,21),(2,11,29),(0,11,30),(2,11,31),(1,4,234),(2,11,32),(2,11,33),(2,11,34),(2,11,46),(2,11,48),(1,1,12),(1,2,12),(1,4,12),(1,12,17),(3,12,20),(1,12,21),(1,12,29),(3,12,30),(1,12,31),(3,4,249),(1,12,32),(1,12,33),(1,12,34),(1,12,46),(1,12,48),(3,1,13),(3,2,13),(3,3,13),(2,13,34),(2,13,21),(0,13,26),(2,13,43),(2,13,23),(2,13,27),(1,1,28),(2,13,28),(3,0,145),(2,13,32),(2,13,33),(2,13,41),(1,1,14),(1,2,14),(1,3,14),(1,14,23),(3,14,26),(1,14,27),(1,14,28),(3,14,30),(1,14,33),(1,14,34),(1,14,41),(1,14,43),(1,1,15),(1,2,15),(1,3,15),(1,4,15),(3,4,284),(3,4,285),(1,1,80),(2,26,46),(2,26,48),(3,1,105),(0,5,105),(3,0,106),(1,27,46),(1,27,48),(3,0,118),(1,1,123),(2,30,41),(2,30,43),(1,1,60),(3,1,138),(3,1,144),(1,32,41),(1,32,43),(3,1,156),(3,0,157),(3,1,66)]
def h0W : BT Decor := buildWiresBT 9 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[],[(2,3),(0,1)]]
def h0Autos : BT (List (Nat × Nat)) := btOfList 1 h0AutoList
lemma h0Pairs : goodPairs h0G h0Pos h0Neg := goodPairs_of (by decide +kernel)
lemma h0BaseOk : ∀ x ∈ h0Base, faithful h0Pos h0Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
lemma h0WOk : btAll (fun x => faithful h0Pos h0Neg x ∧ x.1 < 2^128) h0W := buildWiresBT_faithful h0BaseOk
lemma h0AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h0G = h0G) h0Autos := btAll_ofList (autos_of (by decide +kernel))
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 1,6),some (subcubeFast 0 2,6),some (subcubeFast 0 4,7),some (subcubeFast 0 8,7),some (subcubeFast 0 16,6),some (subcubeFast 0 32,9),some (subcubeFast 1 0,9),some (subcubeFast 1 2,5),some (subcubeFast 1 4,5),some (subcubeFast 1 16,4),some (subcubeFast 1 32,6),some (subcubeFast 2 0,9),some (subcubeFast 2 1,5),some (subcubeFast 2 8,5),some (subcubeFast 2 16,4),some (subcubeFast 2 32,6),some (subcubeFast 4 0,8),some (subcubeFast 4 1,5),some (subcubeFast 4 8,5),some (subcubeFast 4 16,5),some (subcubeFast 4 32,5),some (subcubeFast 6 0,5),some (subcubeFast 6 1,4),some (subcubeFast 8 0,8),some (subcubeFast 8 2,5),some (subcubeFast 8 4,5),some (subcubeFast 8 16,5),some (subcubeFast 8 32,5),some (subcubeFast 9 0,5),some (subcubeFast 9 2,4),some (subcubeFast 12 0,5),some (subcubeFast 12 16,4),some (subcubeFast 12 32,4),some (subcubeFast 16 0,8),some (subcubeFast 16 1,5),some (subcubeFast 16 2,5),some (subcubeFast 16 4,5),some (subcubeFast 16 8,5),some (subcubeFast 16 32,5),some (subcubeFast 17 0,5),some (subcubeFast 17 2,4),some (subcubeFast 18 0,5),some (subcubeFast 18 1,4),some (subcubeFast 20 0,5),some (subcubeFast 20 8,4),some (subcubeFast 20 32,4),some (subcubeFast 24 0,5),some (subcubeFast 24 4,4),some (subcubeFast 24 32,4),some (subcubeFast 32 0,8),some (subcubeFast 32 4,5),some (subcubeFast 32 8,5),some (subcubeFast 33 0,5),some (subcubeFast 33 4,4),some (subcubeFast 34 0,5),some (subcubeFast 34 8,4),some (subcubeFast 48 0,5),some (subcubeFast 48 4,4),some (subcubeFast 48 8,4),some (0xaa55aa55aa55aa55aa55aa55aa55aa55,9),some (0xaaaaaaaa55555555aaaaaaaa55555555,9),some (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3,9),some (0xcccccccc33333333cccccccc33333333,9),some (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f,9),some (0xff0000ffff0000ffff0000ffff0000ff,9),some (0xffff00000000ffffffff00000000ffff,8),some (0x66666666666666666666666666666666,8),some (0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a,9),some (0x55aa55aa55aa55aa55aa55aa55aa55aa,9),some (0x5555aaaa5555aaaa5555aaaa5555aaaa,9),some (0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c,9),some (0x33cc33cc33cc33cc33cc33cc33cc33cc,9),some (0x3333cccc3333cccc3333cccc3333cccc,9),some (0xffffffff00000000ffffffff0000,9)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 7 h0SliceList
def h0Specs : List PoolSpec := poolSteps h0Steps [(6,[]),(11,[]),(6,[17]),(11,[17]),(11,[17,18]),(0,[]),(16,[0]),(5,[0,17,18]),(16,[]),(61,[17,18]),(23,[0]),(59,[]),(59,[0]),(34,[]),(1,[]),(61,[0]),(5,[0,17]),(2,[]),(61,[17]),(6,[17,30]),(59,[0,30]),(11,[17,30]),(61,[0,30]),(23,[0,30]),(5,[17,0,30]),(3,[]),(36,[]),(50,[]),(33,[0,30]),(17,[]),(23,[]),(59,[17]),(6,[40]),(35,[]),(11,[40]),(24,[]),(16,[40]),(23,[40,53]),(37,[]),(49,[17]),(5,[17,53]),(49,[0]),(59,[40,53]),(43,[]),(23,[40]),(5,[17]),(5,[0]),(6,[17,55]),(11,[17,55]),(49,[]),(5,[]),(33,[]),(59,[40]),(33,[17]),(6,[40,58]),(11,[40,58]),(5,[0,58]),(60,[17]),(5,[17,59]),(33,[0]),(6,[42]),(11,[42]),(16,[42]),(23,[42]),(51,[]),(38,[]),(59,[42]),(45,[]),(63,[0]),(5,[17,65]),(19,[]),(6,[17,48]),(11,[17,48]),(2,[48]),(61,[17,48]),(64,[0]),(3,[48]),(59,[17,48]),(4,[]),(6,[45,17,48]),(6,[45]),(11,[45,17,48]),(11,[45]),(63,[0,45]),(64,[0,45]),(49,[17,48]),(57,[]),(5,[17,48]),(60,[17,48]),(6,[17,45]),(59,[0,45]),(11,[17,45]),(61,[0,45]),(16,[0,45]),(23,[0,45]),(33,[0,45]),(6,[17,45,71]),(11,[17,45,71]),(6,[17,51]),(11,[17,51]),(2,[51]),(61,[17,51]),(3,[51]),(59,[17,51]),(33,[17,51]),(6,[17,51,73]),(11,[17,51,73]),(16,[0,73]),(5,[0,17,73]),(23,[0,73]),(20,[]),(60,[17,51]),(66,[]),(5,[0,17,55]),(6,[20]),(11,[20]),(2,[0]),(5,[0,20]),(61,[20]),(3,[0]),(59,[20]),(53,[]),(33,[20]),(61,[0,43]),(59,[0,43]),(8,[]),(63,[]),(32,[]),(31,[]),(2,[0,45]),(2,[0,46]),(33,[0,46]),(63,[0,44]),(39,[]),(5,[20,76]),(30,[]),(6,[20,78]),(6,[20,77]),(11,[20,77]),(16,[77]),(61,[20,77]),(23,[77]),(59,[20,77]),(49,[20,77]),(5,[20,77]),(60,[20,77]),(52,[]),(13,[]),(61,[]),(11,[20,78]),(16,[78]),(61,[20,78]),(23,[78]),(59,[20,78]),(49,[20,78]),(5,[20,78]),(60,[20,78]),(6,[20,45]),(11,[20,45]),(49,[20]),(3,[0,45]),(6,[45,20,84]),(11,[45,20,84]),(16,[0,45,84]),(23,[0,45,84]),(5,[20]),(5,[20,0]),(60,[20]),(6,[20,46]),(11,[20,46]),(6,[46]),(11,[46]),(16,[0,46]),(23,[0,46]),(3,[0,46]),(63,[0,46]),(16,[0,46,47]),(23,[0,46,30]),(6,[20,84]),(11,[20,84]),(16,[0,84]),(23,[0,84]),(5,[0,20,84]),(6,[30,47]),(11,[30,47]),(16,[0,47]),(5,[0,30,47]),(6,[21]),(11,[21]),(5,[0,21]),(61,[21]),(59,[21]),(55,[]),(33,[21]),(6,[21,101]),(11,[21,101]),(2,[101]),(61,[21,101]),(23,[101]),(59,[21,101]),(5,[0,21,101]),(58,[]),(49,[21,101]),(5,[21,101]),(60,[21,101]),(6,[21,45]),(11,[21,45]),(49,[21]),(5,[21]),(60,[21]),(6,[21,102]),(11,[21,102]),(23,[0,102]),(5,[0,21,102]),(6,[23]),(11,[23]),(11,[23,103]),(63,[0,103]),(5,[0,23,103]),(61,[23,103]),(49,[23,103]),(11,[35]),(60,[23,103]),(11,[37]),(18,[]),(11,[45,23,103]),(6,[45,23]),(63,[0,45,103]),(5,[0,23]),(61,[23]),(6,[23,30]),(11,[23,30]),(25,[]),(5,[23,0,30]),(63,[0,30]),(6,[35]),(16,[35]),(33,[35,106]),(26,[]),(49,[23]),(5,[23,106]),(61,[35,106]),(33,[35]),(16,[35,107]),(5,[23,107]),(61,[35,107]),(46,[]),(5,[23]),(6,[23,113]),(11,[23,113]),(61,[35]),(23,[23]),(6,[35,108]),(59,[23]),(5,[23,115]),(6,[37]),(16,[37]),(33,[37]),(27,[]),(61,[37]),(60,[23]),(5,[23,116]),(6,[20,76,95]),(11,[20,76,95]),(2,[95]),(23,[76]),(5,[20,76,95]),(6,[23,44]),(16,[0,44]),(11,[23,44]),(61,[0,44]),(5,[23,0,44]),(23,[0,44]),(6,[23,45]),(11,[23,45]),(56,[]),(63,[0,113]),(5,[0,23,113]),(6,[24]),(11,[24]),(5,[0,24]),(61,[24]),(5,[24,32]),(2,[32]),(3,[24]),(33,[20,96]),(64,[20,96]),(5,[24,33]),(2,[33]),(64,[24]),(59,[24]),(23,[24]),(63,[0,120]),(33,[0,120]),(64,[]),(44,[]),(64,[0,39]),(28,[]),(6,[20,77,96]),(11,[20,77,96]),(16,[77,96]),(5,[20,77,96]),(6,[24,45]),(11,[24,45]),(49,[24]),(6,[45,24,120]),(11,[45,24,120]),(16,[0,45,120]),(33,[0,45,120]),(63,[0,45,120]),(5,[24]),(5,[24,0]),(60,[24]),(6,[24,46]),(11,[24,46]),(64,[0,46]),(6,[46,30,50]),(16,[0,46,50]),(33,[0,46,30]),(63,[0,46,30]),(6,[24,120]),(11,[24,120]),(16,[0,120]),(5,[0,24,120]),(6,[30,50]),(11,[30,50]),(16,[0,50]),(5,[0,30,50]),(6,[25]),(11,[25]),(5,[0,25]),(61,[25]),(63,[20,78]),(5,[25,33]),(63,[33]),(61,[33]),(64,[25]),(59,[25]),(49,[25]),(5,[25,107]),(5,[25]),(63,[35]),(47,[]),(23,[25]),(5,[25,135]),(33,[37,110]),(26,[110]),(5,[25,110]),(63,[37,110]),(63,[37]),(60,[25]),(33,[37,136]),(5,[25,136]),(6,[20,78,80]),(11,[20,78,80]),(2,[80]),(5,[20,78,80]),(5,[25,62]),(63,[42,62]),(63,[42]),(61,[42]),(6,[25,44]),(11,[25,44]),(5,[25,0,44]),(6,[25,45]),(11,[25,45]),(6,[25,134]),(11,[25,134]),(5,[0,25,134]),(33,[0,134]),(6,[26]),(11,[26]),(5,[0,26]),(61,[26]),(23,[26]),(59,[26]),(6,[26,140]),(11,[26,140]),(16,[140]),(61,[26,140]),(5,[0,26,140]),(59,[26,140]),(49,[26,140]),(5,[26,140]),(60,[26,140]),(6,[26,45]),(11,[26,45]),(49,[26]),(5,[26]),(60,[26]),(6,[26,141]),(11,[26,141]),(16,[0,141]),(5,[0,26,141]),(6,[27]),(11,[27]),(11,[27,142]),(5,[0,142]),(61,[27,142]),(60,[]),(60,[0]),(6,[27,144]),(5,[0,144]),(62,[]),(62,[0]),(60,[27,144]),(61,[27]),(23,[27]),(59,[27]),(6,[27,146]),(11,[27,146]),(5,[0,146]),(2,[146]),(61,[27,146]),(59,[27,146]),(33,[27,146]),(49,[147]),(5,[146,147]),(5,[146]),(60,[27,146]),(33,[27]),(6,[27,148]),(11,[27,148]),(2,[148]),(61,[27,148]),(23,[27,148]),(59,[27,148]),(5,[0,148]),(5,[148]),(60,[27,148]),(60,[27]),(6,[27,149]),(11,[27,149]),(5,[0,149]),(6,[28]),(11,[28]),(61,[28]),(23,[28]),(59,[28]),(49,[0,38]),(5,[0,38,152]),(5,[0,38]),(60,[0,38]),(3,[28]),(5,[0,38,157]),(6,[28,152]),(11,[28,152]),(16,[152]),(61,[28,152]),(5,[0,152]),(59,[28,152]),(33,[28,152]),(49,[153]),(5,[152,153]),(5,[152]),(60,[28,152]),(49,[0,154]),(5,[0,152,154]),(33,[28]),(49,[0,43]),(5,[0,43,155]),(5,[0,43]),(60,[0,43]),(5,[0,43,160]),(69,[28]),(6,[28,44]),(6,[44]),(60,[0,44]),(11,[28,44]),(11,[44]),(62,[0,44]),(5,[0,44]),(63,[28]),(49,[0,44]),(64,[28]),(5,[0,44,155]),(49,[0,159]),(5,[0,155,159]),(6,[28,155]),(11,[28,155]),(16,[155]),(61,[28,155]),(23,[28,155]),(59,[28,155]),(5,[0,155]),(5,[155]),(60,[28,155]),(49,[0,158]),(5,[0,155,158]),(60,[28]),(6,[28,156]),(11,[28,156]),(16,[0,156]),(5,[0,156]),(49,[0,161]),(5,[0,156,161]),(6,[29]),(11,[29]),(5,[0,29]),(6,[20,84,85]),(11,[20,84,85]),(49,[0,29]),(5,[0,29,62]),(2,[42]),(60,[0,29]),(5,[0,29,163]),(6,[24,120,126]),(11,[24,120,126]),(0,[24]),(12,[24]),(73,[0,45]),(6,[29,45]),(11,[29,45]),(6,[29,45,67]),(3,[0,45,67]),(23,[0,29,45]),(63,[0,45,67]),(33,[0,29,45]),(63,[0,29,45]),(5,[0,29,67]),(5,[0,68]),(23,[0,29]),(63,[0,29]),(33,[0,29]),(10,[]),(6,[29,46]),(11,[29,46]),(61,[0,46]),(67,[]),(6,[30]),(11,[30]),(5,[0,30]),(6,[30,49]),(11,[30,49]),(16,[0,49]),(5,[0,30,49]),(6,[30,39]),(6,[39]),(11,[39]),(11,[30,39]),(16,[0,39]),(63,[0,39]),(33,[0,39]),(64,[0,30]),(49,[0,39]),(5,[0,39]),(49,[0,30]),(6,[30,44]),(11,[30,44]),(6,[30,45]),(11,[30,45]),(6,[30,46]),(11,[30,46]),(68,[]),(11,[40,52]),(5,[0,52]),(61,[40]),(6,[40,53]),(11,[40,53]),(5,[0,53]),(61,[40,53]),(5,[53]),(60,[40,53]),(60,[40]),(6,[42,62]),(11,[42,62]),(5,[0,62]),(61,[42,62]),(23,[42,62]),(59,[42,62]),(33,[62]),(5,[62]),(60,[42,62]),(49,[0,137]),(5,[0,62,137]),(60,[42]),(6,[42,64]),(11,[42,64]),(33,[0,64]),(5,[0,64]),(48,[]),(6,[43]),(11,[43]),(6,[43,75]),(11,[43,75]),(5,[0,43,75]),(16,[0,43]),(6,[43,45]),(11,[43,45]),(6,[43,46]),(11,[43,46]),(69,[]),(6,[44,45]),(11,[44,45]),(16,[0,44,45]),(63,[0,44,45]),(23,[0,44,45]),(64,[0,44,45]),(6,[45,69]),(6,[44,46]),(11,[44,46]),(6,[45,67]),(11,[45,67]),(5,[0,67]),(5,[0,67,166]),(11,[45,69]),(5,[0,69]),(6,[45,67,166]),(6,[45,46]),(11,[45,46]),(65,[]),(11,[3]),(6,[10]),(61,[3]),(5,[3,10]),(6,[10,172]),(16,[172]),(11,[3,172]),(33,[3,10]),(4,[3]),(5,[3,10,172]),(35,[3]),(6,[11]),(29,[]),(6,[11,32]),(16,[32]),(6,[32]),(0,[11]),(11,[3,32]),(11,[32]),(61,[3,32]),(1,[3]),(23,[3,11]),(33,[3,11]),(64,[3,11]),(40,[]),(49,[3,11]),(5,[3,11]),(42,[]),(6,[11,37]),(60,[3,11]),(11,[3,37]),(61,[3,37]),(62,[3,11]),(67,[11]),(6,[11,42]),(11,[3,42]),(61,[3,42]),(6,[11,173]),(11,[3,173]),(26,[3]),(5,[3,11,173]),(2,[173]),(63,[3]),(6,[11,174]),(11,[3,174]),(34,[11]),(5,[3,11,174]),(6,[12]),(16,[12]),(23,[3]),(2,[12]),(6,[12,24]),(11,[3,24]),(23,[3,24]),(63,[12]),(33,[3]),(64,[3,24]),(6,[24,12,178]),(16,[12,178]),(6,[12,178]),(2,[12,178]),(63,[12,178]),(61,[3,24]),(63,[3,12]),(49,[3,24]),(5,[3,24]),(62,[3,24]),(6,[24,12,180]),(6,[12,180]),(11,[24,3,180]),(63,[3,12,180]),(6,[12,25]),(0,[25]),(11,[3,25]),(23,[3,25]),(61,[3,12]),(64,[3,25]),(49,[3,25]),(5,[3,25]),(62,[3,25]),(6,[25,12,180]),(11,[25,3,180]),(61,[3,12,180]),(22,[]),(61,[3,25]),(5,[3,12]),(3,[3]),(59,[12]),(33,[12]),(3,[42]),(49,[12]),(60,[12]),(49,[3]),(62,[3]),(67,[12]),(6,[12,171]),(6,[171]),(11,[3,171]),(23,[3,171]),(16,[171]),(61,[3,171]),(3,[3,171]),(4,[12]),(64,[12]),(64,[3,171]),(49,[3,171]),(5,[3,171]),(62,[3,171]),(5,[12]),(71,[3]),(64,[3]),(5,[3]),(11,[3,180]),(16,[12,180]),(23,[3,180]),(5,[3,12,180]),(59,[3]),(6,[13]),(16,[13]),(2,[13]),(5,[3,13]),(59,[13]),(33,[13]),(63,[13]),(49,[13]),(5,[13]),(60,[13]),(6,[13,185]),(11,[3,185]),(16,[13,185]),(5,[3,13,185]),(6,[14]),(16,[14]),(2,[14]),(5,[3,14]),(7,[]),(6,[14,32]),(16,[14,32]),(0,[14]),(1,[32]),(23,[14]),(3,[14]),(59,[14,32]),(64,[3,14]),(49,[14,32]),(5,[14,32]),(60,[14,32]),(6,[32,14,187]),(11,[32,3,187]),(11,[3,187]),(64,[3,14,187]),(41,[]),(59,[14]),(6,[14,170]),(6,[170]),(11,[3,170]),(33,[3,170]),(16,[170]),(61,[3,170]),(19,[170]),(64,[3,170]),(64,[14]),(49,[3,170]),(5,[3,170]),(62,[3,170]),(49,[14]),(5,[14]),(63,[14]),(60,[14]),(6,[14,187]),(16,[14,187]),(33,[3,187]),(5,[3,14,187]),(72,[]),(6,[15]),(16,[15]),(2,[15]),(5,[3,15]),(23,[15]),(59,[15]),(63,[15]),(49,[15]),(5,[15]),(60,[15]),(6,[15,190]),(11,[3,190]),(16,[15,190]),(5,[3,15,190]),(6,[16]),(16,[16]),(60,[3]),(6,[16,169]),(60,[3,169]),(16,[16,169]),(2,[16]),(5,[3,169]),(62,[3,169]),(23,[16]),(59,[16]),(6,[16,192]),(16,[16,192]),(11,[3,192]),(11,[192]),(5,[3,192]),(59,[16,192]),(33,[16,192]),(63,[16,192]),(5,[192]),(60,[16,192]),(33,[16]),(63,[16]),(60,[16]),(15,[]),(6,[169]),(16,[169]),(6,[32,169]),(61,[32]),(11,[32,3]),(63,[3,169]),(23,[3,169]),(33,[3,169]),(64,[3,169]),(49,[3,169]),(62,[32]),(5,[32]),(12,[]),(6,[37,169]),(2,[37]),(11,[37,3]),(62,[37]),(6,[42,169]),(11,[42,3]),(62,[42]),(6,[24,118]),(16,[118]),(33,[3,118]),(24,[3]),(5,[3,24,118]),(63,[3,118]),(6,[25,133]),(33,[3,133]),(5,[3,25,133]),(2,[133]),(6,[25,184]),(11,[3,25,184]),(33,[3,184]),(5,[3,25,184]),(6,[31]),(16,[31]),(11,[3,31,195]),(2,[31,195]),(16,[31,195]),(5,[3,31,195]),(64,[3,195]),(63,[31,195]),(11,[3,31]),(2,[31]),(5,[3,31]),(11,[31]),(59,[31]),(63,[31]),(49,[31]),(5,[31]),(60,[31]),(6,[31,196]),(11,[3,31,196]),(16,[31,196]),(5,[3,31,196]),(64,[3,196]),(5,[3,32]),(59,[32]),(63,[32]),(6,[32,171]),(11,[32,3,171]),(16,[32,171]),(5,[32,3,171]),(49,[32]),(60,[32]),(6,[32,175]),(11,[3,32,175]),(16,[32,175]),(23,[3,175]),(33,[3,175]),(5,[3,32,175]),(64,[3,175]),(6,[33]),(16,[33]),(11,[3,33]),(5,[3,33]),(11,[33]),(6,[33,121]),(16,[33,121]),(3,[121]),(59,[33,121]),(33,[121]),(63,[33,121]),(49,[33,121]),(5,[33,121]),(60,[33,121]),(11,[3,33,197]),(64,[3,197]),(59,[33]),(6,[33,170]),(59,[3,170]),(11,[33,3,170]),(16,[33,170]),(5,[33,3,170]),(49,[33]),(5,[33]),(60,[33]),(6,[33,198]),(11,[3,33,198]),(16,[33,198]),(33,[3,198]),(5,[3,33,198]),(6,[34]),(16,[34]),(11,[3,34]),(2,[34]),(5,[3,34]),(11,[34]),(59,[34]),(63,[34]),(6,[34,171]),(11,[34,3,171]),(16,[34,171]),(5,[34,3,171]),(63,[3,171]),(49,[34]),(5,[34]),(60,[34]),(6,[34,199]),(11,[3,34,199]),(16,[34,199]),(23,[3,199]),(5,[3,34,199]),(11,[3,35]),(2,[35]),(6,[35,105]),(16,[35,105]),(5,[3,105]),(3,[105]),(59,[35,105]),(33,[35,105]),(63,[35,105]),(5,[105]),(60,[35,105]),(54,[]),(59,[35]),(6,[35,170]),(11,[35,3,170]),(16,[35,170]),(60,[35]),(6,[35,200]),(11,[3,35,200]),(16,[35,200]),(5,[3,200]),(6,[37,109]),(16,[37,109]),(5,[3,109]),(23,[109]),(59,[37,109]),(33,[37,109]),(63,[37,109]),(5,[109]),(60,[37,109]),(59,[37]),(60,[37]),(6,[37,176]),(11,[3,37,176]),(16,[37,176]),(23,[3,176]),(5,[3,176]),(71,[]),(6,[170,188]),(11,[3,170,188]),(2,[188]),(16,[170,188]),(23,[3,188]),(5,[3,170,188]),(11,[3,40]),(2,[40]),(63,[40]),(6,[40,171]),(60,[3,171]),(11,[40,3,171]),(16,[40,171]),(6,[40,201]),(11,[3,40,201]),(16,[40,201]),(5,[3,201]),(6,[42,61]),(16,[42,61]),(5,[3,61]),(23,[42,61]),(59,[42,61]),(33,[61]),(63,[42,61]),(5,[61]),(60,[42,61]),(6,[42,63]),(16,[42,63]),(11,[42,63]),(2,[42,63]),(5,[3,63]),(59,[42,63]),(33,[63]),(63,[42,63]),(5,[63]),(60,[42,63]),(6,[42,171]),(11,[42,3,171]),(16,[42,171]),(6,[42,177]),(11,[3,42,177]),(16,[42,177]),(33,[3,177]),(5,[3,177]),(11,[4]),(61,[4]),(6,[10,32]),(0,[10]),(11,[4,32]),(61,[4,32]),(1,[4]),(23,[4,10]),(33,[4,10]),(64,[4,10]),(4,[4]),(49,[4,10]),(5,[4,10]),(63,[4,10]),(21,[]),(70,[4]),(11,[4,172]),(26,[4]),(5,[4,10,172]),(6,[10,205]),(11,[4,205]),(61,[4,205]),(24,[4]),(35,[4]),(5,[10,4,205]),(59,[4]),(23,[4]),(61,[13]),(5,[4,13]),(33,[4]),(64,[4]),(62,[4]),(5,[4]),(49,[4]),(6,[13,207]),(11,[4,207]),(5,[4,13,207]),(61,[14]),(5,[4,14]),(6,[14,208]),(11,[4,208]),(5,[4,14,208]),(33,[4,208]),(61,[15]),(5,[4,15]),(6,[15,189]),(11,[4,189]),(61,[15,189]),(5,[4,15,189]),(59,[15,189]),(23,[15,189]),(63,[4]),(6,[15,209]),(11,[4,209]),(5,[4,15,209]),(60,[4]),(61,[16]),(15,[32]),(3,[16]),(3,[4]),(15,[4]),(6,[202]),(5,[4,202]),(6,[32,202]),(11,[32,4]),(2,[202]),(63,[4,202]),(23,[4,202]),(33,[4,202]),(64,[4,202]),(49,[4,202]),(11,[4,24]),(5,[4,24]),(33,[4,118]),(5,[4,24,118]),(63,[4,118]),(6,[24,210]),(11,[24,4,210]),(33,[4,210]),(5,[24,4,210]),(11,[4,24,210]),(63,[4,210]),(11,[4,31]),(5,[4,31]),(61,[31]),(6,[20,76,94]),(16,[76]),(64,[4,94]),(6,[31,211]),(11,[4,31,211]),(5,[4,31,211]),(64,[4,211]),(5,[4,32]),(6,[32,119]),(16,[32,119]),(61,[32,119]),(59,[32,119]),(23,[119]),(33,[119]),(63,[32,119]),(60,[32,119]),(5,[32,119]),(49,[32,119]),(6,[32,206]),(11,[4,32,206]),(23,[4,206]),(33,[4,206]),(5,[4,32,206]),(64,[4,206]),(11,[4,33]),(5,[4,33]),(6,[33,212]),(11,[4,33,212]),(33,[4,212]),(5,[4,33,212]),(11,[4,34]),(5,[4,34]),(61,[34]),(23,[4,77]),(6,[34,214]),(11,[4,34,214]),(23,[4,214]),(5,[4,34,214]),(11,[4,35]),(5,[4,105]),(61,[35,105]),(6,[35,106]),(11,[4,35,106]),(5,[4,106]),(59,[35,106]),(60,[35,106]),(6,[35,215]),(11,[4,35,215]),(5,[4,215]),(11,[4,37]),(6,[37,216]),(11,[4,37,216]),(23,[4,216]),(5,[4,216]),(6,[203]),(11,[4,203]),(5,[4,203]),(6,[33,212,213]),(23,[4,213]),(64,[4,213]),(11,[4,40]),(11,[4,40,53]),(5,[4,53]),(6,[40,217]),(11,[4,40,217]),(5,[4,217]),(11,[4,42]),(6,[42,218]),(11,[4,42,218]),(33,[4,218]),(5,[4,218]),(6,[204]),(11,[4,204]),(5,[4,204]),(11,[5]),(59,[10]),(61,[5]),(16,[5]),(2,[5]),(23,[10]),(5,[5,10]),(3,[10]),(33,[10]),(64,[10]),(33,[5]),(63,[5]),(49,[10]),(5,[10]),(60,[10]),(49,[5]),(5,[5]),(62,[5]),(6,[10,222]),(11,[5,222]),(16,[5,222]),(23,[10,222]),(5,[5,10,222]),(59,[11]),(5,[5,11]),(23,[11]),(3,[11]),(33,[11]),(64,[11]),(49,[11]),(5,[11]),(60,[11]),(6,[11,223]),(11,[5,223]),(5,[5,11,223]),(23,[11,223]),(5,[5,14]),(64,[5]),(68,[14]),(6,[14,224]),(11,[5,224]),(23,[14,224]),(33,[5,224]),(5,[5,14,224]),(3,[15]),(5,[5,15]),(68,[15]),(64,[15]),(6,[15,225]),(11,[5,225]),(23,[15,225]),(5,[5,15,225]),(60,[5]),(6,[16,191]),(59,[16,191]),(11,[5,191]),(11,[191]),(5,[5,191]),(33,[16,191]),(64,[16,191]),(5,[191]),(60,[16,191]),(64,[16]),(6,[219]),(23,[219]),(6,[24,219]),(11,[24,5]),(16,[5,219]),(33,[5,219]),(63,[5,219]),(64,[5,219]),(49,[5,219]),(5,[5,219]),(62,[24]),(11,[5,23,103]),(3,[23,103]),(23,[23,103]),(5,[5,23,103]),(63,[5,103]),(59,[23,103]),(64,[23,103]),(11,[5,23]),(3,[23]),(5,[5,23]),(64,[23]),(6,[23,226]),(11,[5,23,226]),(23,[23,226]),(5,[5,23,226]),(63,[5,226]),(11,[5,24]),(5,[5,24]),(6,[24,227]),(11,[5,24,227]),(16,[5,227]),(23,[24,227]),(33,[5,227]),(5,[5,24,227]),(63,[5,227]),(11,[5,25]),(3,[25]),(5,[5,25]),(6,[25,228]),(11,[5,25,228]),(23,[25,228]),(33,[5,228]),(5,[5,25,228]),(11,[5,26]),(3,[26]),(5,[5,26]),(64,[26]),(6,[26,230]),(11,[5,26,230]),(16,[5,230]),(23,[26,230]),(5,[5,26,230]),(11,[5,27]),(3,[27]),(64,[27]),(6,[27,231]),(11,[5,27,231]),(23,[27,231]),(5,[5,231]),(11,[5,28]),(6,[28,232]),(11,[5,28,232]),(16,[5,232]),(23,[28,232]),(5,[5,232]),(6,[220]),(11,[5,220]),(23,[220]),(5,[5,220]),(70,[]),(6,[25,228,229]),(16,[5,229]),(14,[]),(63,[5,229]),(11,[5,40]),(3,[40]),(64,[40]),(6,[40,233]),(11,[5,40,233]),(23,[40,233]),(5,[5,233]),(11,[5,42]),(3,[42,62]),(5,[5,62]),(64,[42,62]),(64,[42]),(6,[42,234]),(11,[5,42,234]),(23,[42,234]),(33,[5,234]),(5,[5,234]),(6,[221]),(11,[5,221]),(23,[221]),(5,[5,221]),(11,[6]),(61,[6]),(16,[6]),(5,[6,11]),(33,[6]),(5,[6]),(49,[6]),(6,[11,238]),(11,[6,238]),(5,[6,11,238]),(5,[6,14]),(64,[6]),(6,[14,237]),(11,[6,237]),(5,[14,6,237]),(16,[6,237]),(61,[6,237]),(62,[6]),(6,[14,239]),(11,[6,239]),(33,[6,239]),(5,[6,14,239]),(5,[6,15]),(63,[6]),(6,[15,237]),(5,[15,6,237]),(6,[15,240]),(11,[6,240]),(5,[6,15,240]),(60,[6]),(6,[16,237]),(6,[237]),(60,[6,237]),(5,[6,237]),(62,[6,237]),(3,[237]),(6,[235]),(6,[24,235]),(11,[24,6]),(16,[6,235]),(33,[6,235]),(63,[6,235]),(3,[235]),(64,[6,235]),(49,[6,235]),(5,[6,235]),(6,[28,235]),(60,[6,235]),(11,[28,6]),(62,[6,235]),(62,[28]),(6,[42,235]),(11,[42,6]),(11,[6,23]),(5,[6,23]),(6,[23,237]),(11,[23,6,237]),(5,[23,6,237]),(63,[6,237]),(6,[23,241]),(11,[6,23,241]),(5,[6,23,241]),(63,[6,241]),(11,[6,24]),(2,[6]),(5,[6,24]),(6,[24,242]),(11,[6,24,242]),(16,[6,242]),(33,[6,242]),(5,[6,24,242]),(63,[6,242]),(11,[6,25]),(5,[6,25]),(6,[25,237]),(11,[25,6,237]),(5,[25,6,237]),(6,[25,243]),(11,[6,25,243]),(33,[6,243]),(5,[6,25,243]),(11,[6,26]),(5,[6,26]),(6,[26,245]),(11,[6,26,245]),(16,[6,245]),(5,[6,26,245]),(11,[6,27]),(11,[6,27,146]),(5,[6,146]),(6,[27,246]),(11,[6,27,246]),(5,[6,246]),(11,[6,28]),(6,[28,247]),(11,[6,28,247]),(16,[6,247]),(5,[6,247]),(6,[236]),(11,[6,236]),(5,[6,236]),(6,[25,243,244]),(16,[6,244]),(63,[6,244]),(11,[6,40]),(6,[40,56]),(59,[40,56]),(11,[6,40,56]),(5,[6,56]),(16,[40,56]),(6,[40,248]),(11,[6,40,248]),(5,[6,248]),(11,[6,42]),(6,[42,249]),(11,[6,42,249]),(33,[6,249]),(5,[6,249]),(11,[7]),(69,[14]),(5,[7,14]),(6,[14,28]),(60,[7,14]),(11,[7,28]),(1,[7]),(62,[7,14]),(16,[7,14]),(2,[7]),(49,[7,14]),(51,[14]),(23,[7,14]),(70,[7]),(6,[14,186]),(33,[186]),(11,[7,186]),(63,[7]),(5,[7,14,186]),(25,[7]),(50,[7]),(16,[7]),(61,[7]),(23,[7]),(64,[7]),(49,[7]),(5,[7]),(62,[7]),(6,[15,20]),(0,[15]),(11,[7,20]),(16,[7,15]),(23,[7,15]),(63,[7,20]),(49,[7,15]),(5,[7,15]),(63,[7,15]),(6,[15,28]),(60,[7,15]),(62,[7,15]),(63,[7,28]),(51,[15]),(11,[7,189]),(5,[7,15,189]),(12,[189]),(6,[15,37]),(11,[7,37]),(63,[7,37]),(6,[15,252]),(11,[7,252]),(33,[252]),(23,[15,7]),(18,[15]),(5,[15,7,252]),(6,[15,254]),(11,[7,254]),(17,[15]),(5,[7,15,254]),(69,[15]),(60,[7]),(11,[7,191]),(5,[7,191]),(63,[16,191]),(23,[16,191]),(3,[7]),(11,[7,192]),(5,[7,192]),(6,[250]),(6,[20,250]),(11,[20,7]),(16,[7,250]),(23,[7,250]),(33,[250]),(63,[7,250]),(49,[7,250]),(5,[7,250]),(62,[20]),(6,[24,250]),(11,[24,7]),(64,[7,250]),(5,[24,7,250]),(6,[28,250]),(60,[7,250]),(11,[28,7]),(62,[7,250]),(6,[32,250]),(11,[32,7]),(5,[32,7,250]),(6,[37,250]),(11,[37,7]),(6,[42,250]),(11,[42,7]),(15,[7]),(11,[7,17,18]),(33,[17,18]),(5,[7,17,18]),(63,[17,18]),(59,[7]),(11,[7,17]),(5,[7,17]),(63,[17]),(11,[7,17,48]),(5,[7,17,48]),(11,[7,17,51]),(63,[17,51]),(6,[17,257]),(11,[7,17,257]),(33,[17,257]),(5,[7,17,257]),(5,[7,20]),(63,[20]),(6,[20,255]),(11,[7,20,255]),(16,[7,255]),(23,[7,255]),(33,[20,255]),(5,[7,20,255]),(11,[7,21]),(5,[7,21]),(63,[21]),(11,[7,21,101]),(23,[7,101]),(5,[7,21,101]),(6,[21,258]),(11,[7,21,258]),(23,[7,258]),(33,[21,258]),(5,[7,21,258]),(6,[22]),(33,[22]),(11,[7,22]),(5,[7,22]),(11,[22]),(63,[22]),(59,[22]),(49,[22]),(5,[22]),(60,[22]),(6,[22,260]),(11,[7,22,260]),(16,[7,260]),(33,[22,260]),(5,[7,22,260]),(69,[24]),(11,[7,24]),(5,[7,24]),(33,[118]),(16,[7,118]),(5,[7,24,118]),(63,[7,118]),(24,[7]),(63,[118]),(23,[7,24]),(62,[7,24]),(49,[7,24]),(61,[7,24]),(11,[7,25]),(5,[7,25]),(6,[25,251]),(63,[7,251]),(11,[25,7,251]),(33,[251]),(5,[25,7,251]),(11,[7,251]),(11,[7,26]),(5,[7,26]),(6,[26,139]),(16,[7,139]),(5,[7,26,139]),(12,[26]),(6,[26,262]),(11,[7,26,262]),(16,[7,262]),(5,[7,26,262]),(0,[26]),(11,[7,27]),(63,[27]),(11,[7,27,148]),(5,[7,148]),(6,[27,263]),(11,[7,27,263]),(33,[27,263]),(5,[7,263]),(63,[28,152]),(19,[152]),(5,[7,152]),(6,[28,253]),(11,[7,28,253]),(16,[7,253]),(33,[28,253]),(5,[7,253]),(6,[251]),(5,[7,251]),(11,[7,32]),(5,[7,32]),(11,[7,33]),(5,[7,33]),(6,[33,252]),(59,[7,252]),(11,[33,7,252]),(5,[33,7,252]),(64,[7,252]),(11,[7,35]),(6,[35,107]),(11,[7,35,107]),(5,[7,107]),(63,[35,107]),(59,[35,107]),(60,[35,107]),(6,[35,264]),(11,[7,35,264]),(33,[35,264]),(5,[7,264]),(69,[37]),(6,[37,110]),(11,[37,110]),(5,[7,110]),(23,[110]),(59,[37,110]),(5,[110]),(60,[37,110]),(6,[37,256]),(11,[7,37,256]),(23,[7,256]),(33,[37,256]),(5,[7,256]),(6,[252]),(5,[7,252]),(11,[7,42]),(11,[8]),(5,[8]),(60,[8]),(61,[8]),(62,[8]),(16,[8]),(23,[8]),(6,[265]),(6,[20,265]),(11,[20,8]),(16,[8,265]),(23,[8,265]),(63,[8,265]),(49,[8,265]),(5,[8,265]),(6,[28,265]),(60,[8,265]),(11,[28,8]),(62,[8,265]),(6,[37,265]),(11,[37,8]),(64,[8,265]),(59,[8]),(11,[8,17]),(5,[8,17]),(6,[17,267]),(59,[8,267]),(11,[17,8,267]),(16,[8,267]),(5,[17,8,267]),(61,[8,267]),(64,[17]),(11,[8,17,48]),(5,[8,17,48]),(63,[8]),(64,[8]),(11,[8,17,51]),(49,[8]),(64,[17,51]),(6,[17,268]),(11,[8,17,268]),(5,[8,17,268]),(11,[8,20]),(2,[8]),(3,[8]),(5,[8,20]),(64,[20]),(6,[20,269]),(11,[8,20,269]),(16,[8,269]),(23,[8,269]),(5,[8,20,269]),(11,[8,21]),(5,[8,21]),(64,[21]),(11,[8,21,101]),(23,[8,101]),(5,[8,21,101]),(64,[21,101]),(6,[21,270]),(11,[8,21,270]),(23,[8,270]),(5,[8,21,270]),(11,[8,22]),(5,[8,22]),(64,[22]),(6,[22,271]),(11,[8,22,271]),(16,[8,271]),(5,[8,22,271]),(11,[8,24]),(5,[8,24]),(70,[8]),(16,[8,118]),(5,[8,24,118]),(63,[8,118]),(24,[8]),(1,[8]),(6,[24,272]),(11,[24,8,272]),(16,[8,272]),(25,[8]),(5,[24,8,272]),(50,[8]),(11,[8,24,272]),(63,[8,272]),(11,[8,27]),(11,[8,27,148]),(5,[8,148]),(6,[27,273]),(11,[8,27,273]),(5,[8,273]),(11,[8,28]),(6,[28,274]),(11,[8,28,274]),(16,[8,274]),(5,[8,274]),(6,[266]),(11,[8,266]),(5,[8,266]),(11,[8,35]),(64,[35]),(11,[8,35,107]),(5,[8,107]),(6,[35,275]),(11,[8,35,275]),(5,[8,275]),(11,[8,37]),(64,[37]),(6,[37,276]),(11,[8,37,276]),(23,[8,276]),(5,[8,276]),(6,[267]),(11,[8,267]),(5,[8,267]),(11,[9]),(6,[277]),(5,[277]),(6,[24,277]),(11,[24,9]),(5,[24,277]),(16,[9,277]),(33,[9,277]),(63,[9,277]),(23,[9,277]),(64,[9,277]),(10,[24]),(59,[9]),(11,[9,17]),(16,[9]),(23,[9]),(61,[9]),(63,[9]),(64,[9]),(33,[9]),(11,[9,20]),(2,[9]),(3,[9]),(11,[9,21]),(11,[9,22]),(6,[22,259]),(5,[22,259]),(60,[22,259]),(16,[259]),(59,[22,259]),(3,[259]),(33,[22,259]),(62,[9]),(11,[9,23,103]),(5,[23,103]),(63,[9,103]),(11,[9,23]),(11,[9,24]),(5,[24,118]),(60,[24,118]),(59,[24,118]),(23,[24,118]),(11,[9,25]),(11,[9,26]),(6,[278]),(11,[9,278]),(5,[278]),(6,[278,281]),(11,[9,278,281]),(16,[9,281]),(33,[9,278]),(5,[278,281]),(60,[281]),(11,[9,31]),(11,[9,32]),(11,[9,33]),(11,[9,34]),(6,[279]),(11,[9,279]),(5,[279]),(6,[279,282]),(11,[9,279,282]),(23,[9,282]),(33,[9,279]),(5,[279,282]),(60,[282]),(6,[280]),(11,[9,280]),(5,[280]),(5,[17,18]),(6,[17,19]),(16,[19]),(5,[17,18,19]),(23,[19]),(6,[17,42]),(60,[17,18]),(62,[17,18]),(2,[18]),(49,[17,18]),(64,[17,18]),(3,[18]),(6,[17,40]),(11,[17,40]),(62,[17]),(6,[17,40,53]),(11,[17,40,53]),(6,[17,40,59]),(11,[17,40,59]),(11,[17,42]),(6,[17,42,65]),(11,[17,42,65]),(33,[17,65]),(11,[20,74]),(16,[74]),(23,[74]),(5,[20,74]),(6,[20,283]),(16,[74,283]),(23,[74,283]),(2,[283]),(5,[20,74,283]),(3,[283]),(6,[20,40]),(11,[20,40]),(6,[40,20,78]),(11,[40,20,78]),(16,[40,78]),(23,[40,78]),(64,[20,78]),(6,[20,40,284]),(11,[20,40,284]),(16,[40,284]),(23,[40,284]),(5,[20,284]),(6,[20,42]),(11,[20,42]),(6,[42,20,78]),(11,[42,20,78]),(16,[42,78]),(23,[42,78]),(6,[20,42,285]),(11,[20,42,285]),(16,[42,285]),(23,[42,285]),(33,[20,285]),(5,[20,285]),(6,[20,76]),(11,[20,76]),(2,[93]),(11,[20,76,93]),(16,[76,93]),(23,[76,93]),(63,[20,93]),(63,[93]),(5,[20,76,93]),(6,[20,83]),(11,[20,83]),(16,[83]),(23,[83]),(11,[21,99]),(23,[99]),(5,[21,99]),(6,[21,286]),(16,[286]),(5,[21,99,286]),(23,[99,286]),(3,[286]),(6,[42,21]),(60,[21,99]),(62,[21,99]),(63,[21,99]),(2,[99]),(49,[21,99]),(64,[21,99]),(33,[21,99]),(6,[21,287]),(16,[287]),(3,[287]),(11,[21,99,287]),(6,[21,100]),(23,[100]),(5,[21,100]),(11,[21,288]),(16,[288]),(5,[21,100,288]),(23,[100,288]),(3,[288]),(6,[21,40]),(11,[21,40]),(62,[21]),(6,[21,40,289]),(11,[21,40,289]),(23,[40,289]),(5,[21,289]),(6,[21,42]),(11,[21,42]),(6,[21,42,62]),(11,[21,42,62]),(33,[21,62]),(5,[21,62]),(6,[21,42,290]),(11,[21,42,290]),(23,[42,290]),(33,[21,290]),(5,[21,290]),(6,[23,104]),(16,[104]),(63,[103,104]),(5,[23,103,104]),(33,[104]),(63,[103]),(6,[35,23]),(62,[23,103]),(63,[35,103]),(6,[23,35,106]),(5,[23,103,106]),(2,[103]),(63,[35,106]),(63,[103,35,106]),(4,[103]),(6,[23,35,107]),(5,[23,103,107]),(63,[103,35,107]),(6,[37,23]),(63,[37,103]),(6,[23,112]),(5,[23,112]),(11,[23,291]),(16,[291]),(63,[112,291]),(5,[23,112,291]),(33,[291]),(63,[112]),(60,[23,112]),(11,[37,23]),(3,[23,112]),(62,[23,112]),(2,[112]),(49,[23,112]),(23,[23,112]),(64,[23,112]),(6,[23,35]),(11,[23,35]),(62,[23]),(11,[23,35,106]),(11,[23,35,107]),(6,[23,35,115]),(11,[23,35,115]),(63,[35,115]),(6,[23,37]),(11,[23,37]),(6,[23,37,116]),(11,[23,37,116]),(23,[23,116]),(63,[37,116]),(3,[1]),(16,[1]),(63,[1]),(64,[1]),(49,[1]),(5,[1]),(63,[95]),(11,[24,117]),(16,[117]),(33,[117]),(5,[24,117]),(6,[24,292]),(16,[117,292]),(2,[292]),(63,[117,292]),(5,[24,117,292]),(33,[117,292]),(63,[117]),(11,[24,193]),(16,[118,193]),(2,[193]),(63,[118,193]),(5,[24,118,193]),(33,[118,193]),(6,[24,32]),(11,[24,32]),(6,[24,33]),(11,[24,33]),(9,[]),(6,[24,35]),(11,[24,35]),(5,[24,105]),(64,[35,105]),(43,[35]),(49,[20,77,96]),(6,[24,35,293]),(11,[24,35,293]),(16,[35,293]),(33,[35,293]),(5,[24,293]),(63,[35,293]),(6,[24,37]),(11,[24,37]),(5,[24,109]),(64,[37,109]),(6,[24,37,111]),(11,[24,37,111]),(2,[37,111]),(16,[37,111]),(23,[24,111]),(5,[24,111]),(63,[37,111]),(6,[24,37,294]),(11,[24,37,294]),(16,[37,294]),(23,[24,294]),(33,[37,294]),(5,[24,294]),(63,[37,294]),(2,[2]),(64,[2]),(11,[17,48,66]),(3,[2]),(16,[66]),(2,[130]),(6,[17,48,66]),(16,[66,130]),(33,[17,130]),(63,[66,130]),(64,[130]),(2,[131]),(16,[66,131]),(33,[17,131]),(63,[66,131]),(4,[131]),(64,[24,131]),(64,[131]),(63,[66]),(2,[1]),(6,[24,42]),(11,[24,42]),(33,[54]),(2,[295]),(5,[24,295]),(11,[40,53,54]),(5,[53,295]),(16,[40,295]),(33,[54,295]),(63,[54,295]),(63,[54]),(11,[25,132]),(33,[132]),(5,[25,132]),(6,[25,296]),(16,[296]),(63,[296]),(5,[25,132,296]),(33,[132,296]),(33,[133]),(5,[25,133]),(11,[25,194]),(16,[194]),(63,[194]),(5,[25,133,194]),(33,[133,194]),(6,[25,33]),(11,[25,33]),(5,[20,78,79]),(6,[25,35]),(11,[25,35]),(5,[25,105]),(62,[25]),(6,[25,35,107]),(11,[25,35,107]),(6,[25,35,135]),(11,[25,35,135]),(33,[35,135]),(6,[25,37]),(11,[25,37]),(6,[25,37,110]),(11,[25,37,110]),(23,[25,110]),(6,[25,37,136]),(11,[25,37,136]),(23,[25,136]),(16,[36]),(33,[36,20]),(63,[36]),(6,[25,42]),(11,[25,42]),(6,[25,42,62]),(11,[25,42,62]),(11,[26,138]),(16,[138]),(5,[26,138]),(6,[26,297]),(16,[138,297]),(2,[297]),(63,[297]),(5,[26,138,297]),(33,[297]),(16,[139]),(5,[26,139]),(11,[26,261]),(16,[139,261]),(2,[261]),(63,[261]),(5,[26,139,261]),(33,[261]),(60,[26,139]),(11,[37,26]),(62,[26,139]),(49,[26,139]),(23,[26,139]),(64,[26,139]),(6,[26,35]),(11,[26,35]),(62,[26]),(6,[26,35,298]),(11,[26,35,298]),(16,[35,298]),(5,[26,298]),(6,[26,37]),(11,[26,37]),(6,[26,37,111]),(11,[26,37,111]),(23,[26,111]),(5,[26,111]),(6,[26,37,299]),(11,[26,37,299]),(16,[37,299]),(23,[26,299]),(5,[26,299]),(5,[142]),(6,[27,143]),(16,[143]),(5,[142,143]),(5,[144]),(11,[27,145]),(16,[145]),(5,[144,145]),(6,[27,146,147]),(11,[27,146,147]),(16,[147]),(23,[27,147]),(5,[150]),(11,[28,150]),(16,[150]),(6,[28,300]),(16,[150,300]),(2,[300]),(5,[150,300]),(6,[28,151]),(16,[151]),(5,[151]),(11,[28,301]),(16,[151,301]),(2,[301]),(5,[151,301]),(6,[28,152,153]),(11,[28,152,153]),(2,[153]),(16,[152,153]),(23,[28,153]),(5,[52]),(6,[40,168]),(33,[168]),(5,[52,168]),(5,[60]),(11,[42,60]),(33,[60]),(6,[42,302]),(33,[60,302]),(5,[60,302])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 12 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
lemma h0Slice73 : Slice h0R h0G (0xffffffff00000000ffffffff0000) 9 := opposite_slice (oppositeRow 4 5 47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
lemma h0Slice72 : Slice h0R h0G (0x3333cccc3333cccc3333cccc3333cccc) 9 := opposite_slice (oppositeRow 1 4 61) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
lemma h0Slice71 : Slice h0R h0G (0x33cc33cc33cc33cc33cc33cc33cc33cc) 9 := opposite_slice (oppositeRow 1 3 61) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
lemma h0Slice70 : Slice h0R h0G (0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c) 9 := opposite_slice (oppositeRow 1 2 61) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h61Bound
set_option maxRecDepth 200000 in
lemma h0Slice69 : Slice h0R h0G (0x5555aaaa5555aaaa5555aaaa5555aaaa) 9 := opposite_slice (oppositeRow 0 4 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h79Bound
set_option maxRecDepth 200000 in
lemma h0Slice68 : Slice h0R h0G (0x55aa55aa55aa55aa55aa55aa55aa55aa) 9 := opposite_slice (oppositeRow 0 3 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h80Bound
set_option maxRecDepth 200000 in
lemma h0Slice67 : Slice h0R h0G (0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a) 9 := opposite_slice (oppositeRow 0 2 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h81Bound
set_option maxRecDepth 200000 in
lemma h0Slice66 : Slice h0R h0G (0x66666666666666666666666666666666) 8 := opposite_slice (oppositeRow 0 1 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h82Bound
set_option maxRecDepth 200000 in
lemma h0Slice65 : Slice h0R h0G (0xffff00000000ffffffff00000000ffff) 8 := mapped_slice (identifyRow 4 5 47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h92Bound
set_option maxRecDepth 200000 in
lemma h0Slice64 : Slice h0R h0G (0xff0000ffff0000ffff0000ffff0000ff) 9 := mapped_slice (identifyRow 3 4 55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h93Bound
set_option maxRecDepth 200000 in
lemma h0Slice63 : Slice h0R h0G (0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f) 9 := mapped_slice (identifyRow 2 4 59) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h108Bound
set_option maxRecDepth 200000 in
lemma h0Slice62 : Slice h0R h0G (0xcccccccc33333333cccccccc33333333) 9 := mapped_slice (identifyRow 1 5 61) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h109Bound
set_option maxRecDepth 200000 in
lemma h0Slice61 : Slice h0R h0G (0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3) 9 := mapped_slice (identifyRow 1 2 61) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h116Bound
set_option maxRecDepth 200000 in
lemma h0Slice60 : Slice h0R h0G (0xaaaaaaaa55555555aaaaaaaa55555555) 9 := mapped_slice (identifyRow 0 5 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h117Bound
set_option maxRecDepth 200000 in
lemma h0Slice59 : Slice h0R h0G (0xaa55aa55aa55aa55aa55aa55aa55aa55) 9 := mapped_slice (identifyRow 0 3 62) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) h118Bound
set_option maxRecDepth 200000 in
lemma h0Slice58 : Slice h0R h0G (subcubeFast 48 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
lemma h0Slice57 : Slice h0R h0G (subcubeFast 48 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
lemma h0Slice56 : Slice h0R h0G (subcubeFast 48 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h119Bound
set_option maxRecDepth 200000 in
lemma h0Slice55 : Slice h0R h0G (subcubeFast 34 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h51Bound
set_option maxRecDepth 200000 in
lemma h0Slice54 : Slice h0R h0G (subcubeFast 34 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h111Bound
set_option maxRecDepth 200000 in
lemma h0Slice53 : Slice h0R h0G (subcubeFast 33 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h120Bound
set_option maxRecDepth 200000 in
lemma h0Slice52 : Slice h0R h0G (subcubeFast 33 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h121Bound
set_option maxRecDepth 200000 in
lemma h0Slice51 : Slice h0R h0G (subcubeFast 32 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h122Bound
set_option maxRecDepth 200000 in
lemma h0Slice50 : Slice h0R h0G (subcubeFast 32 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h123Bound
set_option maxRecDepth 200000 in
lemma h0Slice49 : Slice h0R h0G (subcubeFast 32 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h124Bound
set_option maxRecDepth 200000 in
lemma h0Slice48 : Slice h0R h0G (subcubeFast 24 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
lemma h0Slice47 : Slice h0R h0G (subcubeFast 24 4) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
lemma h0Slice46 : Slice h0R h0G (subcubeFast 24 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h100Bound
set_option maxRecDepth 200000 in
lemma h0Slice45 : Slice h0R h0G (subcubeFast 20 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
lemma h0Slice44 : Slice h0R h0G (subcubeFast 20 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
lemma h0Slice43 : Slice h0R h0G (subcubeFast 20 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h127Bound
set_option maxRecDepth 200000 in
lemma h0Slice42 : Slice h0R h0G (subcubeFast 18 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h0Slice41 : Slice h0R h0G (subcubeFast 18 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h128Bound
set_option maxRecDepth 200000 in
lemma h0Slice40 : Slice h0R h0G (subcubeFast 17 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
lemma h0Slice39 : Slice h0R h0G (subcubeFast 17 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h129Bound
set_option maxRecDepth 200000 in
lemma h0Slice38 : Slice h0R h0G (subcubeFast 16 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
lemma h0Slice37 : Slice h0R h0G (subcubeFast 16 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h130Bound
set_option maxRecDepth 200000 in
lemma h0Slice36 : Slice h0R h0G (subcubeFast 16 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h131Bound
set_option maxRecDepth 200000 in
lemma h0Slice35 : Slice h0R h0G (subcubeFast 16 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h39Bound
set_option maxRecDepth 200000 in
lemma h0Slice34 : Slice h0R h0G (subcubeFast 16 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h132Bound
set_option maxRecDepth 200000 in
lemma h0Slice33 : Slice h0R h0G (subcubeFast 16 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h133Bound
set_option maxRecDepth 200000 in
lemma h0Slice32 : Slice h0R h0G (subcubeFast 12 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h101Bound
set_option maxRecDepth 200000 in
lemma h0Slice31 : Slice h0R h0G (subcubeFast 12 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
lemma h0Slice30 : Slice h0R h0G (subcubeFast 12 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h137Bound
set_option maxRecDepth 200000 in
lemma h0Slice29 : Slice h0R h0G (subcubeFast 9 2) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h54Bound
set_option maxRecDepth 200000 in
lemma h0Slice28 : Slice h0R h0G (subcubeFast 9 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h138Bound
set_option maxRecDepth 200000 in
lemma h0Slice27 : Slice h0R h0G (subcubeFast 8 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h139Bound
set_option maxRecDepth 200000 in
lemma h0Slice26 : Slice h0R h0G (subcubeFast 8 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
lemma h0Slice25 : Slice h0R h0G (subcubeFast 8 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h140Bound
set_option maxRecDepth 200000 in
lemma h0Slice24 : Slice h0R h0G (subcubeFast 8 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h55Bound
set_option maxRecDepth 200000 in
lemma h0Slice23 : Slice h0R h0G (subcubeFast 8 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h141Bound
set_option maxRecDepth 200000 in
lemma h0Slice22 : Slice h0R h0G (subcubeFast 6 1) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
lemma h0Slice21 : Slice h0R h0G (subcubeFast 6 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h145Bound
set_option maxRecDepth 200000 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 4 32) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h146Bound
set_option maxRecDepth 200000 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 4 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 4 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h147Bound
set_option maxRecDepth 200000 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 4 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h148Bound
set_option maxRecDepth 200000 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 4 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h149Bound
set_option maxRecDepth 200000 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 2 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h150Bound
set_option maxRecDepth 200000 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 2 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 2 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h60Bound
set_option maxRecDepth 200000 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 2 1) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h89Bound
set_option maxRecDepth 200000 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 2 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h151Bound
set_option maxRecDepth 200000 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 1 32) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h155Bound
set_option maxRecDepth 200000 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h156Bound
set_option maxRecDepth 200000 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 1 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h157Bound
set_option maxRecDepth 200000 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 1 2) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h91Bound
set_option maxRecDepth 200000 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 1 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h158Bound
set_option maxRecDepth 200000 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 0 32) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h159Bound
set_option maxRecDepth 200000 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 0 16) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h164Bound
set_option maxRecDepth 200000 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 8) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h165Bound
set_option maxRecDepth 200000 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 4) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h167Bound
set_option maxRecDepth 200000 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 2) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h168Bound
set_option maxRecDepth 200000 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 1) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h169Bound
lemma h0SlicesOk : btAll (sliceSpec h0R h0G) h0Slices := btAll_ofList (P := sliceSpec h0R h0G) (sliceSpecCons h0Slice0 (sliceSpecCons h0Slice1 (sliceSpecCons h0Slice2 (sliceSpecCons h0Slice3 (sliceSpecCons h0Slice4 (sliceSpecCons h0Slice5 (sliceSpecCons h0Slice6 (sliceSpecCons h0Slice7 (sliceSpecCons h0Slice8 (sliceSpecCons h0Slice9 (sliceSpecCons h0Slice10 (sliceSpecCons h0Slice11 (sliceSpecCons h0Slice12 (sliceSpecCons h0Slice13 (sliceSpecCons h0Slice14 (sliceSpecCons h0Slice15 (sliceSpecCons h0Slice16 (sliceSpecCons h0Slice17 (sliceSpecCons h0Slice18 (sliceSpecCons h0Slice19 (sliceSpecCons h0Slice20 (sliceSpecCons h0Slice21 (sliceSpecCons h0Slice22 (sliceSpecCons h0Slice23 (sliceSpecCons h0Slice24 (sliceSpecCons h0Slice25 (sliceSpecCons h0Slice26 (sliceSpecCons h0Slice27 (sliceSpecCons h0Slice28 (sliceSpecCons h0Slice29 (sliceSpecCons h0Slice30 (sliceSpecCons h0Slice31 (sliceSpecCons h0Slice32 (sliceSpecCons h0Slice33 (sliceSpecCons h0Slice34 (sliceSpecCons h0Slice35 (sliceSpecCons h0Slice36 (sliceSpecCons h0Slice37 (sliceSpecCons h0Slice38 (sliceSpecCons h0Slice39 (sliceSpecCons h0Slice40 (sliceSpecCons h0Slice41 (sliceSpecCons h0Slice42 (sliceSpecCons h0Slice43 (sliceSpecCons h0Slice44 (sliceSpecCons h0Slice45 (sliceSpecCons h0Slice46 (sliceSpecCons h0Slice47 (sliceSpecCons h0Slice48 (sliceSpecCons h0Slice49 (sliceSpecCons h0Slice50 (sliceSpecCons h0Slice51 (sliceSpecCons h0Slice52 (sliceSpecCons h0Slice53 (sliceSpecCons h0Slice54 (sliceSpecCons h0Slice55 (sliceSpecCons h0Slice56 (sliceSpecCons h0Slice57 (sliceSpecCons h0Slice58 (sliceSpecCons h0Slice59 (sliceSpecCons h0Slice60 (sliceSpecCons h0Slice61 (sliceSpecCons h0Slice62 (sliceSpecCons h0Slice63 (sliceSpecCons h0Slice64 (sliceSpecCons h0Slice65 (sliceSpecCons h0Slice66 (sliceSpecCons h0Slice67 (sliceSpecCons h0Slice68 (sliceSpecCons h0Slice69 (sliceSpecCons h0Slice70 (sliceSpecCons h0Slice71 (sliceSpecCons h0Slice72 (sliceSpecCons h0Slice73 sliceSpecNil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 200000 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (6 - 1) xs.toFinset) h0Empty := trivial
def h0Block6_0 : List NodeSpec := indexPairNodes [(479359,6593), (1642559,4127556385), (1650751,0), (1459822687,64641), (281115679,66817), (1090681887,67329), (306247743,0), (348194879,14657), (6455487,51120449), (88289343,6465), (306251839,0), (348190783,11375020353), (381749311,0), (122618789,113409), (307167925,113409), (93602037,0), (1892479,0), (85365370399,54401), (77381727,300545), (1350629439,0), (1300301887,0), (21877777439,21633), (5303681119,0), (511155761239,9046337), (123498169375,21633), (2004940863,18387965313), (7986102487,40634689), (429979735,254542753), (2055272511,0), (2038529055,66817), (2021722175,0), (27615453335,0)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test6_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 6 h0Block6_0 = true := by decide +kernel
def h0Nodes6 : List NodeSpec := h0Block6_0
lemma h0Check6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 6 h0Nodes6 = true := h0Test6_0
def h0Bucket6 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes6
set_option maxRecDepth 200000 in
lemma h0Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 6 xs.toFinset) h0Bucket6 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check6
def h0Block7_0 : List NodeSpec := indexPairNodes [(612393431,17062560977), (65089663,132404129), (174073983,0x73041198208c31), (975103,862291761191), (56717439,260719521), (2146559,55458885022761), (1898559,2198219785769), (602175,28252033), (111212607,0x7f84498260629), (618559,1043073), (2382741855,2289166377), (696356991,14966786625), (2900223,730094276645417), (2315665759,27652137), (59257919,4631118033), (176698431,64569553), (3780735,500432732321), (2670847,13304545), (608196735,32244945), (2572543,251298589737), (1057439935,266631944233), (1450111,0x1b408b82e1c4045147), (2867455,0xb4085c06440a1), (2248589503,4664209449), (2181513407,253642270761), (2703615,2232193), (331413567,0x3d10543a10be19c53a1), (460863,0x7ea2042018541), (2919710911,48053367849), (2986819775,0x6880c2102e0629), (2834687,0xa7c17063220b729), (2998527,29545770025)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_0 = true := by decide +kernel
def h0Block7_1 : List NodeSpec := indexPairNodes [(9194029557,0x322700a8150b869), (8925659637,1751809), (981594229,8141917065257), (2801918423,0x3f340920140a1), (2835472735,0xf270d402e0241), (2634059903,1977628577), (717260927,0x58a602e010281831), (3784959,8542958469171), (2566967423,55969465249), (3817727,0x7630f10409603429), (4261462447,0xcf40460d1503c1), (3926081967,288074321896489), (3372360031,13291160961), (255087679,34910168028545), (2768302207,933490847658657), (4112639,5640164545065), (255611967,230871007809), (48304255,447582576801), (885037183,22028449), (3389472959,816196891689), (4047103,43909793), (1266743359,0x1f2300782a1462be186010d1), (4786239,0xf8d80d4408403123a1), (10939220159,48053367849), (11073437887,0x6880c2102e0629), (914514391,882625349345), (2768396639,0x1b9029e03220241), (700491903,0x35a02105c02062e1), (8880383,462585348500521), (2869060055,68212228833), (8945919,0x762481a23402c29), (629301719,221220438753)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_1 = true := by decide +kernel
def h0Block7_2 : List NodeSpec := indexTripleNodes [(9666815,8239742883731497,2), (15368143279,0x681007a02429,2), (10322175,0xb1107c80ea02429,2), (10060031,0xeeb004401829,2), (10125567,494666401,2), (15099871583,239847157801,2), (10518783,0x939020c02902c29,2), (14965686623,24066048507945,2), (3774984319,0xad401f01c042941,2), (10453247,504627937,2), (10387711,7730106241,2), (10584319,0x371803e070105be0a29,2), (10649855,0x63068580c3c529,2), (562258391,30837902414377,2), (10715391,0x249a009402c81229,2), (11475927391,4362732929,2), (1367406655,0xeb9000e0446be0382229,6), (2734805119,0xc980d1b0dba0c31,2), (24160303191,0x3ea43e40321c8781c0629,2), (12617022527,0xb4400f05c2c8338241,2), (13153893439,0x26a02a09f0060d1,2), (323080407,0x1ade1e20061e1b0f090f0629,2), (9011455,1657274529,2), (188934207,0x68fb0014120b00c3a1,2), (102857759,0x3ebc601e021e1a162229,2), (197243007,0xc604f8052106416120a1,2), (12812479,0x29c08f806601c0b21,6), (16307896511,0x5e81ae01bc051781,2), (10911999,0xec8800d02902c29,2), (90245183,0x264060806a88108062e0629,2), (98633791,0x1211c0064074f0508062e0629,2), (331789109399,0xffc140922f81b700141,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_2 = true := by decide +kernel
def h0Block7_3 : List NodeSpec := indexTripleNodes [(5251346647,0x1e30a8123e00d600a13031,2), (5217800407,0x3a8450a8125e00dc04a02e031,2), (9294671999,454703425,2), (14336127,1197223643713,2), (14303359,1197223643713,6), (43696255,0x7b203ac01941,2), (60473471,5674899777,2), (20870881375,0x7cc028083802280382c3e1,2), (14294196351,27229436145,2), (6504575,0x19a2002500340c84e0d0e7,2), (934170593375,182737440001,2), (52882620543,27229436145,2), (37715959935,1718617841,2), (30687447,0x1fb9200a60733006f80d40241,2), (76824671,0x7e4d8072f00fec00e11400e0241,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Block7_3 = true := by decide +kernel
def h0Nodes7 : List NodeSpec := h0Block7_0 ++ h0Block7_1 ++ h0Block7_2 ++ h0Block7_3
lemma h0Check7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket6 7 h0Nodes7 = true := by
  unfold h0Nodes7 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨h0Test7_0,h0Test7_1⟩,h0Test7_2⟩,h0Test7_3⟩
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket6Ok h0Check7
def h0Block8_0 : List NodeSpec := indexTripleNodes [(303605,32748,2), (28332247,2146730176,2), (98578687,0xa269e55fb58c4dd,6), (106967295,0xebf3891508b4739,2), (794879,0x1ae7fde39938f8a627,2), (29891647,0x7fa57c1428f0629,2), (1687743,0x3a7f90580871b144b9,2), (462975,0x2382e1e3090471267,2), (98603263,0x34e8041447432c29,2), (102797567,7409816964301353,2), (473993471,0x3a529080f02504d1,2), (2539775,0xffc8d58d00206684231827,2), (2572543,0xffb1a2b74046e3419e2231827,2), (490770687,0xa42c51d023c0a60a1,2), (26752063,0xfc80a0f9abe0d0b0629,2), (213983423,0x6c5c8082343e6a3c14a2b0629,2), (222372031,0x3fe483a96816030f0629,2), (1400959,0x1fe858d0b1a0b8670386e7,2), (2769151,0x7e5068b660b0c912164467,2), (1082167551,0xeb0518bc091229,2), (778495,0x7c20514d081a0c90b54087,2), (168191,0x4e09d0341922461127,2), (3326207,0x1ffe540c68371a1948238a627,2), (25705535,0xe44c00c0e23410f0d0b0629,2), (1695871,0x7940980982e1a42453267,2), (6783477,0xa5e8dc0085c0a45,2), (7934167,0x1f31011832598469,2), (26276095,0x2b99ab8613701104438139,2), (30470399,0xd62045f0348360ca512c39,2), (3129599,0x3f9c090204320e12c319208e2c527,2), (90247263,0x7fb0aa0125046091a229,2), (23612479,0xe280840711a08781c0629,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Block8_1 : List NodeSpec := indexTripleNodes [(1876095,0x770f502101c0c4e12087127,2), (17895679,0x3920fe06e808dc1808d010d1,2), (19992831,0x1eae03a02370c0810c3010d1,2), (30478591,0x34a414c07098021d038329,2), (32575743,0x2ca27012819181438329,2), (356585727,0x92e0c4008c9801008444a0a1,2), (3162367,0x1f62b02206c14482c683738a0cd08461127,2), (1216418047,0xf2906901300888684a0a1,2), (22565951,0x1d6c00a0f8b410f0d0b0629,2), (180494527,0xf9681f00c7e01150cc68f048562229,2), (188883135,0x789805cf0752d02c061e2229,2), (1990783,0xfb848403418c06074b0c887,2), (3948799,0x3e60aae01684111619224258c7,2), (1619071231,0x55c032301a091229,2), (827647,0x3da80ab814c6836c3291a8087,2), (17903871,0xff78011b830b06358d1,6), (22098175,0x1ea2274010455006220887071,2), (26292479,0x1f123e02385f037034194a3c39,2), (2638079,0x3d0c022064810cd8d06e10a0c904714527,6), (73478399,0xcc284090051b43192358d1,2), (81875039,0x3b3012e85502d0760c629,2), (200959,0x27e03260e343291231827,2), (21519423,0x3a87380f4d410f0d0b0629,2), (4440191,0xf8809400619c3a20c267,2), (9208063,0xffa1d00ac0c864c1c25863020237927,2), (20472895,0x1c020028351410f0d0b0629,2), (4669567,0xfe5017061a05060c4e0c1046627,2), (18678261,8606779017797,2), (18940395,0x3f4ef018c0484453,2), (9601279,0xf7e812012020c818b0cc904714527,6), (9732351,0x1ffc480a60260dc386ca478a627,6), (4931711,0xfbe0328170c4389043867,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_1 = true := by decide +kernel
def h0Block8_2 : List NodeSpec := indexTripleNodes [(22122751,0x1d4de008c064838329,2), (9994495,0xf7e226c02b00e063260a866040461127,6), (32608511,0x1ac24014414244429,2), (34658431,0x3ff6808a280208802140100870629091a229,2), (69308671,0x510c47c00a12020229,2), (10191103,0x3fe900a8013031a0dc278ccf0631827,2), (5161087,0x3caa00c8160e28082e130e1830e7,2), (10256639,0x1e550006008d180428cc91a18467,2), (2801919,0xcfa0028240811a83819428654a1042ae527,2), (28422399,0x6b0a8024806a190e69,2), (4145407,0x3d580160330021a80837220433291216c527,6), (17333311,0x351a4e01cc5043c670d0d1,6), (34662527,0x68c79b62100b202c398a514d1ce1a0c31,2), (18381887,0xf7043802e7808305c030f0d0d1,2), (413823,0x3f7407a0aa0420c85614231827,2), (10025087,0x3ffb3ee8033ca84c969,6), (15267967,0x3e91e204b428020a09a052101c2214b284e69,6), (32507967,0x1ef12500141f357c338a2d0229,2), (69208127,0x3483240173c142018a5020229,6), (1720821,0xcd405520020e1a2045,2), (876799,0xfec2014d08060b6f670dcc27,2), (487551,0x8f01701c3648870c1046627,2), (1024255,0x1ff7480070298d00844563322188c27,2), (1073279,0xf80800f02d02d14830418e7,2), (2113791,0x7e02003c05a3008519990c467,2), (2474239,0xf5f802901e14d082106658c250bcc27,2), (1366079,0x7f404e201a407c5a0878ce28b21,2), (1890367,0x331bc02500320173c00405e3c53a1,2), (452671,0x7bc04f100cc6821e338a2d0229,6), (897151,0x62409c092c28022d80cc6968608f38a2d0229,6), (1370175,0xc0401c801900b9e046018a5020229,6), (755417279,0x746802703f008a8731410283242b0629,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_2 = true := by decide +kernel
def h0Block8_3 : List NodeSpec := indexTripleNodes [(822526143,0xf887004e00f02a198d040a0cd162229,6), (2212095,0xe6c0f2028805206c33c2604d04648c6148c27,2), (2277631,0x3e1503c81ec02c0e80780b2c0619888c112334588827,2), (456767,0x76700e782302140c541,6), (355468503,0xfe9f601360140c3,2), (721487063,0x1ffffd4507003501580a1,2), (889259223,0x1f55c8c308f200783f099805c0a0a1,2), (1057031383,0x1d6d5c8cd4507003500230c0a0a1,2), (357565655,0x3f50c50950fa002d003023,2), (359662807,0x7fc69121ee012e01283023,2), (209913047,0xfe7eaf0248be066807415e00a1,2), (226690263,0xc9fe20448ac2812411c028813e00a1,2), (511804031,0x3f5f062300d80130051018481,2), (669002879,0x3fff60e0933c236008202b008d1045,6), (5947519,0x3ea050285439e00340b8670386e7,6), (186122879,0x7e3054de2c32d0cd04f7004500d806023,2), (6111359,0x1e2068130bb803208b02e1c40418e7,2), (621216863,0x2cffea17832062c2080ac0020781,2), (656424063,0xfffd2811a500b06e400581580463045,2), (6176895,0xf282d0b981b700682201c19c1830e7,2), (6275199,0x3c47301700cc01f013808a04e0c11ace7,2), (5150617835,0xfdfc00c600f050c629,2), (198705791,0x3ff4b408c38b403c800f00d402c34084235333,2), (9227481215,0x3ffe50c41cc0de122005814405c020c608c629,2), (8891977855,0x1fdd91874080a1004201218781300483a19908c629,2), (4278284415,0x766f2461d3c06605902480b806a01e14c610a28c629,2), (121111767,0x3f8a027001008504a80140c3,2), (273679575,0x1fa581e83e0d010a09700183023,2), (380634327,0x7d90290260440fb008e05101283023,2), (403703029,0x1fa685b03b050c300220da9,2), (6471807,0xf88930142c09300e901041ace7,2), (18723397727,0x7a4b01db3d0070d80c40085c050a529,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_3 = true := by decide +kernel
def h0Block8_4 : List NodeSpec := indexPairNodes [(5783679,0x1fe04049c01c160e20220082423836e7), (62128767,0x3ff46202211870b04c1a09ee006a004220b18c33), (18454978735,0x3e32017762014c101b050208229), (6537343,0x3f2203b01604f80620aa0620485c08608d4e7), (18454995039,0xfb2ac076930156016201701408229), (6570111,0x3f62840443e1f0558074809c182356e7), (53740159,0x3ff52602205034149810a09d6014705e016070b18c33), (18186576047,0x790280640665500b00cc02e80da0245811229), (6602879,0x784082005821e006a02e1820d4e7), (55837311,0x3ff7a022050e7c261468284801900d80b0682118c33), (5816447,0x1f1b001e0292500510098045c290d636e7), (6209663,0x1fda80d9802880841a34620231827), (17649786975,0xf5682ec02e2a0f812c028808203201808229), (6635647,0x3e88d00f8126009c0911ace7), (15336063,0xffb20a901102870b06870d04158034690d0518c33), (15860351,0x3ff098044250a2d01d601a094008e68682106333), (17381384287,0xf501680442a0470013004101900c1229), (5849215,0x3f79003603bc01620668a432714e7), (188910807,0xfffa90806a71cf00b201831), (353373399,0x7445c9e807aa004a200c3), (1639987415,0x1fb29200e39e0114050105), (6832255,0xe211a00f40fe8011705c33830418e7), (6865023,0x79940021b881e50020d033830418e7), (389024983,0x3f8404200880050035808828da3), (6897791,0x778084011c078c0241e04e0c11ac7), (277120639,0x1f505901682c2c17c07c403a81), (11442073727,0x3ffec10603e4680caf00dc04a02e010631c59a9), (120065239,0x7518020c73018a07703ca00940a80c3), (6257979607,0x1f85025200cb00741540c50141831), (94899415,0x7140d0c6b00b2078f280150161940c3), (6963327,0x3f7068901b2012600a2025c0820d4e7), (60556927,0x7fe282e1d4346e01ac0e1803c1f0086c0235333)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_4 = true := by decide +kernel
def h0Block8_5 : List NodeSpec := indexPairNodes [(6799487,0xfd9067c012e00a600938121041b6e7), (6996095,0xf46010f40094012600a602f024270608d4e7), (124259543,0xee010b09c402c8193e00be00a8110420963), (7061631,0x3f906c20e009201fb00970270608d947), (53216895,0x3b702b24192207d65c05f023600302603c2f02c0e1635333), (107482327,0xfc900d601dc07e80132c0506403810c0c3), (7094399,0x1e981610083805f01f05c33858d4e7), (7127167,0x7990233001e001019f05c33858d947), (7028863,0x3ec3ac016e009a036058420d1a2e2c388827), (25955543,0x37e0340e2017c02602c8b00ae01501719380c3), (7159935,0x3ef029e01fb009703628c11ac7), (7192703,0xf076006bc021c670608d4e7), (7323775,0x3ee30b60052801580b82e0b8670386e7), (7356543,0x1f478457005dc01900d02e1a4245147), (7389311,0x1fd18028d411b00d3401b01820a6e7), (7422079,0x1e4141f1008d8053007404e0c11b6e7), (195562111,0x1ff2416709090063008d00dc18c0ec1e0e0c118c33), (3279984767,0x7fffc0c1000740090a6591017010a0408c629), (103290101,0x7f020718e0066801511c0220da9), (7454847,0x3f8881cf18046c00981140320520411b6e7), (7487615,0x7f6200e60046806507a00c81a6c36e7), (7520383,0x7d3300478c024200a200c8148631b6e7), (7585919,0x3fa181a0e60046802b803205c5811b6e7), (7618687,0x3d6503c6011b002601280b869091b6e7), (7651455,0x7ed80e07300348025016e02e1480436e7), (7553151,0x1fb0614a008d802b8084190a416231827), (7684223,0x1e80c00fe0046807780b810c11b6e7), (15075967,0x70501270975005d01c90b806e0a2200e03e0d0ac1c1822433), (7716991,0xf9fa003602340362077010c1b6e7), (7848063,0x3b21e0110200e780242505c3481045147), (1874884703,0x7c400e000201871c980588011b82845), (7880831,0x1e5a802e3300da003607a1408a6e7)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_5 = true := by decide +kernel
def h0Block8_6 : List NodeSpec := indexPairNodes [(7465865311,0x188a31a40d19007c17f00088008440301045), (7913599,0x7680c600bf018201083a406202356e7), (3716159615,0x7fa28c4b011c07b80b0a41294c023802b803501909c0211045), (3548420223,0xffc902d02a6008f008f0070d32ba0350170286c8c629), (3481327743,0xfebe241ff007a807867fc12c05114024270c8c629), (12985659519,0x3497f8907c403822022c0490170750286a0246531843042229), (7197495391,0x1e782d402140173004b6017033208229), (7946367,0x1f78123e0090802605ec0320520471947), (7979135,0x7e860801d4154060f0342808d947), (7130402911,0xe105414e400bf00a55058805c050a529), (8011903,0x7da05823e005f80529c0190290d11b6e7), (8077439,0x1e704c070664000900f8803206202356e7), (294657199,0x35a016e00a402f00b1a200e0c106023), (8110207,0xec4047c003d00a4c02e1a408e36e7), (8142975,0xfe873600bf02e8144094170e20e36e7), (8044671,0x7684d00ed002fc028b81440420c8520946d427), (26483887,0xfbd0385d802f8137006e0250104044c3), (8175743,0x3d50199002ac039402b0e02356e7), (8208511,0x798f002e81cbc1a471011b6e7), (244189279,0x7ff4bf802c707200f096c019a80781), (1505757279,0x7f653c80178040d03), (138428510,0x1ff386a6980bf803700630038e7f04c2e1), (906233951,0x1f55490d62a2006e06c80784b600940b122e1), (1530923103,0x3b87142242009100a4031801281383), (3020163167,0x3d3aa8c68a6980bf80042004081a80940b122e1), (7969181791,0x7fc0f80612e0004805), (2076182623,0x1f98481060eb000e80c8805301281383), (773850239,0x3e183a820c5880a4b7300aa00c60010f834780418c33), (778044543,0xe582b483086803d2a7301d50090b8360e3084e0c33), (3867170943,0x3ff0e01d6004fc01d0b04d240b819208c629), (3800078463,0x3d7f070264054c001d001c3995103500681701418c33), (3732985983,0xfa7f070048031801ea01e29fe04b0004021214848c629)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_6 = true := by decide +kernel
def h0Block8_7 : List NodeSpec := indexPairNodes [(14663299199,0xf427f0700eb007c36073032bc026c008382c18e0c33), (14327795839,0x645895e0e01c6004ac600420340808c0643a18c70629), (13992292479,0xf4613f83806e80121dc08b003e03a8082004714c6380c33), (6031605,0x3e34048a80223001a05b6d), (87033951,0x3360511c10052090802880841a140a0383), (23332415,0x190a8094620023c01a6bc82c3432b031), (16941183,0x3d280a31000c600fc070ce1208d4e7), (16810111,0xfdf05e0a3c01ed00e1703380436e7), (396363871,0xf8817011c100520eb8008c381082b04c3), (17006719,0x3fb817046200908021804a069091b6e7), (17137791,0x3f9c0d15380206014c0e17038808d4e7), (467667039,0x7d7f004639c01140a403c081805302f01d03), (202938779743,0x1febfe0083b400a100cd008810400e0641), (7600165079,0x7eb4c00a5502104e051229), (18352223,0x4436200d4800b403), (1111492703,0x3d680b002335600ee075401281383), (2143291487,0xfcc40086c40148322014c090340686c3), (1186990175,0xce4011c1005200980692da0308108361183), (17334399,0x1e7a0231000c600fc070ce1208d4e7), (610272383,0x7de01a0f4830cf8008e01dd889b011c064a0d838b022433), (8339583,0x1f630147803da01c2e0520c714e7), (29460832431,0x1f2701312000d0094008a6c142429), (421529695,0xfd9c07436200c4804e0a48010b0d0383), (17399935,0xf75016180206014c04a0670608d4e7), (217056383,0x7f2d0068291041867c011d00ccc0ee0333e0d83c222433), (16875647,0x1f3b017e8015600860240d0290b1b6e7), (4118829183,0xffe198060c009f803a1609bf8020ce88c629), (3984644223,0x1ffdc29800c6007a8078a7f830403706318c629), (15334428799,0xf4abb9568012ab017200840240816406e330970629), (8405405871,0xfe00c003b400e11408411229), (84940895,0x1f50ee600a411b00b701a141408656023), (22809151,0x3c82841405ae0023c01a6b8c1a18d031)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_7 = true := by decide +kernel
def h0Block8_8 : List NodeSpec := indexPairNodes [(17662079,0xe183ed8024200a200981a70f8a627), (17727615,0xfec85002c47813858db627), (392173663,0x1ee146c37300520eb8008f3803834106023), (17793151,0x1fe0f07b600f5800700c814848db627), (17858687,0xf78160aa072e0049800d017404106a627), (463476831,0x3fae063580ff802281dc027400183), (8338354271,0x7f8e068a000c0c40170040e031), (1178605663,0x758361b98029004c03496d00e401206c29a16023), (17989759,0xea40f6c002500268019027091c1827), (18055295,0x3e501ff003480f83ac04e04b8a627), (417339487,0x3dc023617093350077011a0138352400858686743), (18120831,0xf1400d60024c0210120404106a627), (18186367,0xf060719c8006804400f02e0458db627), (4253063295,0x7fff3a00064008e1ccb2203458540828c629), (41423999,0x18c0288014815407b00de015cf650da08634333), (1050678399,0x3ff96f8ab0153802f817c0f602180790090b18c33), (396372213,0xfa19dc800c9002544701541a9), (229643391,0xfb1449f88f00fe803140ee04703d81c409301900c18c33), (18514047,0x1fb65002981882954084190bc2231827), (18579583,0xfdbf8014c01a04502100848620231827), (84095,0x1ee2c00ff00340b84618215493), (51394687,0xfec3e802ec400c2026816e00410998f42c3066ad), (306204887,0x349807b600488033804b8b708104d1), (495743,0xe42800a200480cd649a810a627), (1089663,0x3e4b0034b8ce010a627), (18645119,0xfc8edc0045805c23010234433), (1292001375,0x7c970027c0129003180820ae0c844220a1), (18710655,0x1f284009f00acc01623c09c2c6a627), (1224925279,0xf32a0045805c804105706426020a1), (18776191,0xfcce80116028c00780881864e03852010a627), (616585343,0x1fd34c0180800ba08464c9f0110822433), (1302655,0x18ca001a0170196c28211020831827)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_8 = true := by decide +kernel
def h0Block8_9 : List NodeSpec := indexPairNodes [(18841727,0x1fd05400ff00340b846021c4433), (964784255,0x3fe99c3000d81080881440a9016c0104ecc61011219a9), (50600681599,0x3eb788598016b00a900260261219a9), (18972799,0x7f445003dc00d02e198486627), (19038335,0x1e8d800478007821403206c52c6a627), (348180695,0x3d19003fa00a501f409878ca0081160e160a1), (19103871,0x1f42a004b403d04c3c7500438c106a627), (1728639,0x3f1c40077002408607c318e0c33), (2298515583,0x1d9d8020401c5b0021aa008e053a188f80bf01c3e16668da9), (2231423103,0x7c21e802040048ec0242802503903f86889181f80e1e842061a9), (19169407,0xfa5c2006080f7010c0f851a3627), (2533412991,0xffe799004b80b3017202d035017f088230070f432471431), (1400967383,0xdc35b300147658198361a1960a1), (1417744479,0x330538047c03fb0053710c0cc02161a1960a1), (1908863,0x1ece80088318a4b00c190270081827), (1925247,0xf81c01f180090411403204e010a627), (12386687,0x7e5cc001d401f9c0d02c0b0d0238a627), (19234943,0xfc938c004580643c2cc118c33), (6373503,0x1f987002ec060804180643c281045427), (2843777151,0x7e61c008a0594012428c99807c038045244827), (2130747567,0x379c00a2bb01b0528223068d808420a1), (683710591,0x3cba002f802d29d40116007050a8828e07c05c1043646f1), (2063671471,0x18d50010f00788414560529a1706426020a1), (19300479,0xfc6c80091802b052a80c1e06962c6a627), (717265023,0xf3a8007a01a54d8022c02a196f0190058170545044846f1), (1468084319,0x1fefa800903d00c5c02160904aa1), (19366015,0x7f3ae0005a0050a0f4030781cb010a627), (1426277247,0x7b7b001620123640540a1), (893425791,0xfcf980091008900ac72c65d05701f00e010884106333), (901814399,0x3f98a6c0003802f808b0038266544143500381410823585), (12517759,0x6503c3e5cc000bc01ec0a80a241704e04231827), (4865606527,0xf0d801e18f81ec0540a1)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_9 = true := by decide +kernel
def h0Block8_10 : List NodeSpec := indexPairNodes [(9110067327,0x3fd8a002f805480be022c00e1ccb220321c108923585), (19497087,0x1fd62400ff00340c878598e0c33), (6406271,0x7d0f8018e030407b801a0643c2890b627), (457265367,0x6790075600e10d02780f5704604a0a1), (675326079,0x3fa2008900b94ea004900c616b804c0b062105c1043646f1), (1384206431,0x3e680261003b2a08c092c06c34140a1), (4472959,0x7c5e005530258060c813810c6a627), (1434538199,0x3db200d64015c4a00208a01b0121a20a1), (4505727,0xf6f8035100538640680104500c813810c6a627), (10420607,0x6503c3e5cc00e080743008818d0cc8340e0238a627), (1493262511,0x1f16801b40740881923306c2203031), (314659031,0x722c00a901de052a810836090c60a1), (19562623,0x3fd7740015801703e18c118c33), (17203327,0x1f8b600f8401820046005c0f850229427), (3439382655,0x1ff22b8022f0023200b80b900081a0d4048101980387a19908dd1), (19628159,0x1e73c001f400181f05205154064e0484106a627), (1434546271,0x7e3036390063600470114062e010b04812a1), (19693695,0x3f958032a018700340e400700c9c0909c2c6a627), (4735103,0x3e310009bc400d02e010631c4433), (4800639,0x3e3d00120c02e15090b627), (4866175,0x7e230017300fc01884190c41c1827), (19759231,0x7ac92001106017008318234433), (19824767,0x7ecba0020c02e1501045427), (5062783,0x3f7fc00cec0288084190b8b0231827), (5554303,0xf504002f004f7010c008324118c33), (19890303,0x759dc0027b801a02e05a4118c33)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_10 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0 ++ h0Block8_1 ++ h0Block8_2 ++ h0Block8_3 ++ h0Block8_4 ++ h0Block8_5 ++ h0Block8_6 ++ h0Block8_7 ++ h0Block8_8 ++ h0Block8_9 ++ h0Block8_10
lemma h0Check8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Nodes8 = true := by
  unfold h0Nodes8 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0Test8_0,h0Test8_1⟩,h0Test8_2⟩,h0Test8_3⟩,h0Test8_4⟩,h0Test8_5⟩,h0Test8_6⟩,h0Test8_7⟩,h0Test8_8⟩,h0Test8_9⟩,h0Test8_10⟩
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket7Ok h0Check8
def h0Block9_0 : List NodeSpec := indexTripleNodes [(143615,0x55023089c9108c9cf5a55f,6), (168191,0xaa44394ff4c80c58638904622527,2), (176383,0x7d1f9e0d870b03118b0c71208522527,2), (192767,0x7888214486214024058386043192242f2527,2), (200959,0x15430498e760184141b8604332912372527,2), (209151,0x79969e8806406868140a0c08632448522527,6), (217343,0x791fe900c611901810c66312372527,2), (225535,0x5448e9255400204202a0460c732448522527,6), (233727,0x1985121fd0267c0190089501186399224622527,6), (241919,0x710801902c3c150231632a524258927,6), (129151,0x3bb80ba05500c81386c43867,2), (250111,0x1ca600a40b8308c80c586528a6098927,6), (663807,0xf0c40133e0078060b070c73e5b24a9238927,6), (696575,0x2ae0093c0a20078060506e2fe23ccd1638927,6), (712959,0x98f101d406c0340160e1810ccb6a6b18927,6), (372863,0x3c4059640620ba0284021c18c4041247,6), (729343,0x3c405b2407d005066230218ca50218927,6), (194623,23005505,6), (1491135,0xf417408ca5020229,6), (745727,0xfc809c01e018e820830c1194a2d18927,6), (1523903,0x72407500501c5020229,6), (132214,0xf0d805d026c04c18e7,2), (263286,0x34a91308a50018e7,2), (525438,0x1fa3d7e849d219a088b003046a627,6), (688767,0x3ffb230960a4c1a083601440a2b00e1140608db627,2), (754303,0x167b170cf48610960a343c2840d800408380a0d6627,2), (819839,0xffff04612c14e741420d803e053005c0b0b0d6627,2), (885375,0x7b8e266c0281a0a4c242854200873006868b4146a627,2), (5587071,0xb8941a0b6028407f808607c2cc11ac7,2), (5637335,0x54651e0a2000407415408e0283023,2), (5899479,0x2c6142c789807c0344a804402c03023,2), (3736191,0x3ffc838064a05829cf1e243dc01ac00418c1045b33,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Block9_1 : List NodeSpec := indexTripleNodes [(3867263,0xd9b60c60630a7c29cf062ba03601b80b020801020e0b060823333,6), (3998335,0x7a48f5300c940b0539d0901b00108829880d4008380418c1045b33,6), (4129407,0xf4ff320250a7c29cf1a201b00840a200b8050c48823333,2), (8520319,0x2471b900c8c0d050b0480d80638045ce15c074318229b33,2), (9044607,0xc5c01603e0461a7c2870e85480941680d060804c01209c32106333,2), (5619839,0x34a028b4c06e806680d17160418e7,2), (9831039,0xefa00f81181a0a73c68842049019808a01d944ba1823333,2), (10355327,0x4f81184b0539c1c04808814404419e0150081045e63682823333,2), (5652607,0x21c0e2a607480620c202201190c4041247,2), (133238,0x1a718a804871d700a2018e7,2), (624255,0x3ff1092403faec08d803700e1af0220608db627,2), (689791,0x64fce347ac033d8b866d103c47c00c8090cf8041c0506a627,2), (755327,0x7951fa61d701fd450091001e01901e0540b0b0d6627,2), (820863,0x6f0ad30ce80ee222920245c8022f808e012705344106a627,2), (6668415,0xfb04180a400100f607f80b80d03e16608d4e7,2), (5377239,0x690686876c00302d01c9c07011503023,2), (3606143,0x3fc0a15d981b80fa8dc80f1e5002a00418c1045b33,2), (3737215,0x10c020a15cd020d80b2e8044680d4a800f02080af8041c160c106333,2), (3868287,0x3d4050aecc2d81d24688c0082013c11a0330143e0107008318229b33,2), (3999359,0x7c4020a15d5062074c92080655800d0238054028660823333,2), (4130431,0x2dc0fb300a011420035006e00822e85a02824e04874318229b33,2), (8783487,0x97008d0fd509c121401282d01205fc2fc0a24e0484e0c106333,2), (6701183,0x1f1803c0c8806a804d00040d17160418e7,2), (9569919,0xb500870faa04818e018881c3b00be023804c0eca25f823333,2), (10094207,0x30402143f5431a00c200f043c04103117008d5e630406333,2), (6733951,0x3ff004a000100d301c4184062e0c8620208ce7,2), (135294,0x7fffe46017601b824383b8030806e03046a627,2), (266366,0xfff2ce50a600b08f009e03203a02209046a627,2), (625279,0x7386ce54a4018a4315166c20c41e11a01b81d06502e0b06388827,2), (690815,0x3f890c9e5454035d6e046c0166803601604b88827,2), (756351,0x2a07069ca960044029c446981b8245c8024d02080840cc1a270c9c1827,2), (7225471,0x111fc0c100a40d40238053806410c08c0408d947,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_1 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_1 = true := by decide +kernel
def h0Block9_2 : List NodeSpec := indexTripleNodes [(2427519,0xf640b093caee804840050711047831470050d20823333,2), (2558591,0x1d605849a7774007806f0054e226c65106b01705c045860823333,6), (2689663,0x3a7024f2bba00b100e65f218330688a0420b82c24106333,2), (2820735,0x7b7024d38530048d501c8e930129802e0586660823333,2), (2951807,0x381009033caee800440144888263803c03500909c24106333,2), (3082879,0x4780383269c35800340780878654704d0208061280e8344e0c106333,2), (7258239,0x3ff401c401e3003205a188a6e7,2), (9308799,0x1d681e1216798530048e409202680b9c076512d1320433,2), (9833087,0x123b03c243279ba2006c0840c202681b81d00f0170485e63386520433,2), (7291007,0xf23013d00430093007601702100848620208947,6), (270462,0xfe06029220401620200d40486a0441208db627,2), (560767,0x6926b19c01cd890cd8419100a5102505c020c638d427,2), (626303,0x1b28cd62a802badc060805d01ac02c09715427,2), (691839,0x3224560c8033888d3037068804b014be00f03a19938d427,2), (7749759,0x4c120ff805206a00d802d01fe02181186608d947,2), (2297471,0x7d090cd68d802e6008822214700105a41045b33,2), (2428543,0x1d104866901b002962e288297c05c17008318229b33,6), (2559615,0xe300c35a36005f8065116a052a81082e010648229b33,2), (2690687,0x6304c030d264401de0323a2a02a805c0082cc1045b33,2), (2821759,0x75050a15a3600128048c89c80510090e8648229b33,2), (2952831,0x7603829471a579801215720510294403a074318229b33,6), (7782527,0x3c103211980242008c8138698a6e7,2), (9047679,0x25c0a5294a4c88024e00d203b047a2642a33,2), (9571967,0xa90294a3348558014a20717048dcc7a19968a33,6), (7815295,0x28a0606f006780a70108144042010909c18208947,6), (2113630,0x171ef80e480510346c02e8128041c2507,6), (984191,0x1fce09530033d890225e018600820041c0b01827,2), (4210782,0x940619e023a01381b803c0ea802502507,2), (8405118,0x1041dac0eb0058ee2234c0dc122e40102a01217068b1b42c1827,2), (8241279,0x73038075802903502780f203fc04303e18c11ac7,2), (2753663,0xf1e05641840e009e00060011608a94213208a6cab,2), (3540095,0x1b601404a44106207006e0641510054882653649008382c24106333,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_2 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_2 = true := by decide +kernel
def h0Block9_3 : List NodeSpec := indexTripleNodes [(3802239,0x1eb01a0f906103802780fd00f42ddc0a1008382c24106333,2), (4064383,0xfffe03c0e8820c4fa00900818601a1b80c94020e010648229b33,2), (18352223,0x1fa8042121900504011061018b82e1383,6), (9176191,0xf681d104189f400c805e00a962e2883081082e0282433,2), (9700479,0x305015906103802781c60399445a81a2281082e0282433,2), (20449375,0x63e008228f0004c036c0718340686c3,2), (10749055,0x3d20060d906103802780860144888255404102500838690906333,2), (11273343,0x1041a44104640e00dc0c8268030114485470468012030a0080452c690906333,2), (8274047,0xf2086402580574012700aa0620484e1908087,2), (13370495,0xe080180d07441810600b2e824405345014c031020801070a868a33,2), (13894783,0x38a00f03a20c04300650d0580480400300441e80d400838041468a33,2), (14943359,0x1a600d02a961ed002224024020f5011c022e70c40671705c3d0c668a33,2), (15991935,0x12b00cb070f4b0e78055a00c820404a06e0718786a0338b82e19c324833,6), (8306815,0x36101a87c4017600ab00c41a104068c40418e7,6), (37225599,0x32603d10613e801904080441cc04100209b98d9033,2), (8421502,0x7fbc8055c03b888d300781720082d00cc16370ca641827,2), (17465471,0x79cad4003a02780f203fc04303e18c11ac7,2), (2493567,0x3b7308528180b3c007d8008a88844b208a6cab,2), (3279999,0x1f66c849de03010015220609b3f80a189106333,6), (3542143,0x711c5c852dd02f50048401581e85a2200428dd106333,2), (3804287,0x74851640424b903fbca8023e00b60020b12229b33,2), (17307743,0xf7031b0536003e0181d801a0081c023,2), (10226815,0xd20c857ac09f0032400110051222095500b603a3184906333,2), (10751103,0x31829b21acb5801e1684854706607c19e02c6e19c306333,6), (17531007,0xee407a8046600d301f82a805c0ce1908087,2), (14421119,0x60c0b010f5b70011420035007e0129ce2480340f42c4e8a33,2), (15469695,0x3fc1c5b0d6cc80242802505a03418209a00d0370cdb4833,6), (17596543,0x3d701990057c029c04201a02080b1c40418e7,6), (18251903,0x700a0035015407b027c03208607c2cc11ac7,2), (2233471,0xafc8172002a80f6024c02c13494213208a6cab,2), (3019903,0xf4ba106801ec09f0130548872899c81209c32106333,2), (3282047,0x1efe8172002a80f603e80e8216eb01213852106333,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_3 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_3 = true := by decide +kernel
def h0Block9_4 : List NodeSpec := indexTripleNodes [(3544191,0x1cb552284075bca802381ec04301a0540120e8664229b33,2), (3806335,0x230fe8172002a80f600b80e2208f0625a02c61024823333,2), (4068479,0x2105ae8252006503d80bc054304b89b0338023458e810506333,6), (8655999,0xbc17d02e4005501ec08c1cca2344086051008d163482506333,2), (9180287,0x16824ba094801af81ec051c8ef480f416370ca2823333,2), (18317439,0xfd0f78066a00cc1740aa0190120488087,6), (11801727,0x1141aa91a8803551b901e2381ec04f00d603d0cca42a33,2), (12326015,0x20836ba3350068e822c018d9607b03304102d05500468b19c324833,2), (12850303,0x920d548bd401d24688c02381ec0a607a0f815013008d1637199968a33,2), (13374591,0x22836ba2cb007c924100d7c0f60530334058c21b720433,2), (18382975,0x3aa0a4c00498028811a02e809160418e7,6), (18448511,0x3be00560002403d814c0c405809809100810909808087,2), (79999,0x209c00ab000820404d01cc0760a4060b6af,2), (49293439,0x74d00820079005ac03ce004f27cf52082319d,6), (53487743,0xb0c1f8041005ac00e980840209be22c94232410619d,6), (405631,0x30600a600a200f018a4a1b4b0d0e7,6), (219199,3899913195569,6), (1237119,0x3c2a8011a01f040801280138bb0660208b627,2), (228612223,0x7d8f0015221cd932bc0c411823,2), (43014271,0xd64025801415a013a019040130548818269fc1b042d12208c31,2), (47208575,0x6e2012c00a0a4c0116008402780982a442c69240239cc670c841831,2), (237000831,0x1c4804b019900a9401240a442209ca30364208c31,6), (1286271,0x29603f4046600808065f864190b4108087,2), (1302655,0x60c014c005c065b0a084804642f088087,2), (245389439,0x14b00c1400a132d898272c81106c41831,2), (266360959,0xf948028b00260a910e5348102702441831,2), (1646719,0x71660046807c10202a401703b0660208b627,6), (1663103,0x7cf40007003414808e014e008880907608c0408d4e7,2), (88191,0x29603f40466006b801e02720409c2c18e7,2), (40921215,0x7cb00920002014e805ac001a01e81e1f1244406cf16ba208c31,2), (45115519,0x6ccf009203bc01f60054807f80f0f449ec108047398ce14841831,2), (1679487,0x60c014c01b80b6c38108321a140418e7,2)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_4 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_4 = true := by decide +kernel
def h0Block9_5 : List NodeSpec := indexTripleNodes [(1712255,0x27203e1004980d900de0123039a3b0661a3627,2), (1859711,0xd3cc800a6014808e00f200380d0d1d83e18c714e7,6), (13142143,0x3ec8005c01a3801880b994e8a4f800c0387a169041831,2), (15239295,0x3a678009400b33005e0141590823c4448401c30869041831,2), (1581183,0x10ae0057c000e01b0260360487d058e2030e7,6), (1941631,0x3ce604008d00f820405100606202431e8260229427,6), (784373887,0x3cf7900442002a1825c5d05502f807004140c3,2), (1958015,0xe88063fa00f203417c0917202c80100700d0d0d8061e18c11ac7,2), (792762495,0xe88062f40282010b401430450ae82a8108070085450105,2), (8951935,0xc9e800c7c13a0346e00082863933d4418404402041c2a020a1,2), (10000511,0xc808012868ca008850c7788ba0aa02201020e0105020a1,2), (12097663,0xc5e0016800e6005f803e1451b5124045ce2480b82e1e863041831,2), (14194815,0x639000ec014f00e980160543044c65618c3c4d01705c3a58c841831,2), (178296959,0x1d183400a736d45105298191704c140810841831,2), (1597567,0x1af8001c031068040d829e3706d1a140418e7,2), (608213119,0x345193194414106c0a789170388804141831,2), (38836351,0x389c006407b4004201f02a584a2883080c5c0231398da0a0a1,2), (64002175,0x11161800be011b00f300a860922e816809091706434e1c0a1,2), (4374655,0x744e0046807c1f800c0660d12a034540904c0453627,6), (4407423,0x39b4002d0083001403414808e01d82c35806868a8120f0c608d4e7,2), (8956031,0x333e004a1a2980297c90c14f01841700850820a1,6), (11053183,0xae25003ef27401045ce168062105c3d0c9041831,2), (13150335,0x3a59200d5401a64b91602c61a3040a201170ce14841831,2), (1335423,0x35f000380620740881890935068c40418e7,6), (36743295,0x18c30480131cc972d40d114044021c1398d2120a1,2), (104575,0x633005a800864a26200b81c40418e7,2), (4571263,0x3a7b0024c06c80d8748090c760cc0453627,2), (4604031,0x62b802cb00042c81e2e40020bf00d0d1d83e18c11ac7,2), (10008703,0x7c3400bd001840163bb08e0539c3f019380e1e8598208c31,2), (12105855,0x366220059500c180763560e40c1043019380e184364208c31,2), (4636799,0x35f005500cd21014407a0b1c40418e7,6), (4702335,0xacd0023403e0810197880141d833090b627,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_5 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_5 = true := by decide +kernel
def h0Block9_6 : List NodeSpec := indexTripleNodes [(4767871,0x126e0001c00d052023802a4b80640483b07c2cc714e7,2), (4833407,0x1af8007801158c04d00740b8b030e7,6), (4898943,0xc18047014fd81c4184084190d0a030e7,6), (4964479,0xeb94008d00f80ec00e010802b1d83301045427,6), (4997247,0xed6c003417c090f200105380640483b07c2cc11ac7,2), (5030015,0xd7c02381cc40f80e9017160418e7,6), (5128319,0x1830154066904901880b0170210642f088087,6), (438399,0x2c2c001d01b811806e002a0120c76094310453627,2), (446591,0x5f1006ec34c07e0aa01703b14608087,6), (503935,0xec4c001d01881f0386b01f602606290285810453627,6), (520319,0x5dd00592405100aa0620112270608087,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_6 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_6 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0 ++ h0Block9_1 ++ h0Block9_2 ++ h0Block9_3 ++ h0Block9_4 ++ h0Block9_5 ++ h0Block9_6
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := by
  unfold h0Nodes9 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨h0Test9_0,h0Test9_1⟩,h0Test9_2⟩,h0Test9_3⟩,h0Test9_4⟩,h0Test9_5⟩,h0Test9_6⟩
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := indexTripleNodes [(254,0x4d04c00c07b80241d83c10386e7,6), (1150,0x37c04e00180118017033858a6e7,2), (2174,0x4101da00f700d02e0670386e7,6), (4222,0x4207b802600602981ce03383346e7,6), (8318,0x2c44200670386e7,6), (16510,0x1a85aa0034130030023002e0670386e7,6), (32894,0x687c00a6028802e0670386e7,6), (65662,0x2c1c005c80670386e7,6), (75903,0x5a05c0c9e0e199f,6), (88191,0x18cc00d7003c0e3f833830418e7,6), (92287,0x2b40484f0340b819c1830e7,6), (100479,0x5f00208501a05c0ce0d0e7,6), (104575,0x18cc016a0021e26200b819c2c18e7,6), (108671,0x2e2d201a05c0ce0d0e7,6), (112767,0x8c3d200b819c2c18e7,6), (116863,0x49ed00d02e0520d0e7,6), (120959,0x7f0208c00b819c2c18e7,6), (340095,0x92980a200b810824d0e7,6), (356479,0x494c051000c098ce0d0e7,6)]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Nodes10 : List NodeSpec := h0Block10_0
lemma h0Check10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Nodes10 = true := h0Test10_0
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket9Ok h0Check10
def h0Block11_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,50],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test11_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket10 11 h0Block11_0 = true := by decide +kernel
def h0Nodes11 : List NodeSpec := h0Block11_0
lemma h0Check11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket10 11 h0Nodes11 = true := h0Test11_0
def h0Bucket11 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes11
set_option maxRecDepth 200000 in
lemma h0Bucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 11 xs.toFinset) h0Bucket11 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket10Ok h0Check11
set_option maxRecDepth 200000 in
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,9,13),(VAR 3,5,13),(VAR 4,6,22),(VAR 5,5,37)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 9]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 12]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4277071592 * 2 ^ 32 + 4207470728) ||| ((4277071592 * 2 ^ 32 + 4207470728) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4277071592 * 2 ^ 32 + 4207470728) ||| ((4277071592 * 2 ^ 32 + 4207470728) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_46856
theorem PEqualNP.Outside.L_meta_46856 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4207470728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4207470728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_46856.table2_of_lower (4277071592 * 2 ^ 32 + 4207470728) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_46856.low_root
    PEqualNP.Outside.L_meta_46856.wit PEqualNP.Outside.L_meta_46856.wo (by decide)
    PEqualNP.Outside.L_meta_46856.wit_mono PEqualNP.Outside.L_meta_46856.wit_eval s hcs
