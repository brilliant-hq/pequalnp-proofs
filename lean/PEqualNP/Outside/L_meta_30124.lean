import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_30124
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 256
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
lemma bin_lt (d a b : Nat) (ha : a < 2^256) (hb : b < 2^256) : bin d a b < 2^256 := by
  have h1 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x &&& y) < 2^256 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ||| y) < 2^256 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^256 → y < 2^256 → (x ^^^ y) < 2^256 := fun x y hx hy =>
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
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^256 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^256 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^256 ∧ (w.getD i swZero).2.testBit 0 = false := by
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
    (hw : ∀ u ∈ w, u.2 < 2^256 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
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
lemma normPack_lt (f : Wire) : normPack f < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).isLt
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 256 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 256 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^256) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 256 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 256
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
set_option maxRecDepth 4000 in
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
      have ha1 : simple w (normPack a) := (avail_normPack ha).imp id (fun hm => hreps.symm ▸ hm)
      have hb1 : simple w (normPack b) := (avail_normPack hb).imp id (fun hm => hreps.symm ▸ hm)
      exact made_priced w d (false, normPack a) (false, normPack b) hd ha1 hb1
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
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
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
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false) :
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
  ⟨((r.val &&& (255 ^^^ z)) ||| o) % 256, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^256 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 256
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 256 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^256) (hb : b < 2^256) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 256 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^256) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^256 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^256 := hS a (by simp)
    have hblt : b < 2^256 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^256 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^256 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^256 := by
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
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^256) (hGb0 : G.testBit 0 = false)
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
lemma lower_count {roots : List Nat} {T : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (singles : Finset Nat) (ess : ∀ a ∈ singles, Essential T roots a) :
    Lower roots T (singles.card - 1) := by
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
  have hsub : singles ⊆ S := fun a ha' => raw_required run roots a sub (ess a ha')
  have hle := (Finset.card_le_card hsub).trans (live_size run)
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | 7 => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
  | _ => 0
def ALL256 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 256, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL256 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 8) (hj : j < 8) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) (hw : w < 2^256) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 8 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL256 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
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
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) : swapWord i j w < 2^256 := by
  have hi : i < 8 := by omega
  have h1 : (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^256 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL256 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^256 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^256 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^256 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^256 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^256 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 8) (w : Nat) (hw : w < 2^256) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 8)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^256) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^256 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 256
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
    (hT : T < 2^256) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^256) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^256 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^256 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 256
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
  (List.range 8).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr := ((r &&& (255 ^^^ z)) ||| o) % 256
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
  by_cases hr : r < 256
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 256) (ho : o < 256) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 256 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h255 : ((r.val &&& (255 ^^^ z)) ||| o) < 256 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (255 ^^^ z)) < 256 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 8) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (255 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h255
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 8
    · have h7 : (255 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 256) && decide (s < 256) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL256 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL256]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 256 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^256) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^256 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^256) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^256 ∧ a.testBit 0 = false := by
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
def countCheck (roots : List Nat) (T L : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    decide (essPairs.map Prod.fst).Nodup &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2) &&
    decide (L ≤ essPairs.length - 1)
lemma count_of {roots T L essPairs} (ok : countCheck roots T L essPairs = true) :
    Lower roots T L := by
  simp only [countCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨hT, hR⟩, hnd⟩, hess⟩, hle⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hl := lower_count p1 p2 p3 hR' (essPairs.map Prod.fst).toFinset (fun a ha => by
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm))
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [hcard] at hl
  exact fun p bank hr hav => hle.trans (hl p bank hr hav)
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
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^256)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256 := by
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
def evalInput (r : Row) : Fin 8 → Bool := fun i => r.val.testBit i.val
def packInput (x : Fin 8 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat + 128 * (x 7).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    have h6 := Bool.toNat_le (x 6); have h7 := Bool.toNat_le (x 7); omega⟩
lemma evalInput_packInput (x : Fin 8 → Bool) : evalInput (packInput x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) (j : Fin 8),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat + 128 * b7.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6, b7].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
lemma var_testBit (i : Fin 8) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 255 := by
  let seeds : List SWire := (varsOf 255).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^256 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 255).all (fun a => decide (a < 2^256) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^256 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi8 : i < 8 := by simpa using hi2
      have hv : (varsOf 255)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 255)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi8⟩ r
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
    by_cases hr : r < 256
    · have h := hev ⟨r, hr⟩
      simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]
    exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma replace_of_lower (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 255) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : ∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn : (Fin 8 → Bool) → Bool)
    (hEdgeT : ∀ r : Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  have hwEval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x := by
    intro x
    have hx := evalInput_packInput x
    rw [← hx]
    exact (hwEvalR (packInput x)).trans (hEdgeT (packInput x)).symm
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hlt : gates.countP isBin < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput r)).trans (hEdgeT r))
    have hnd : S.toList.Nodup := Finset.nodup_toList S
    have hrun := live_to_run hlive S.toList hnd (by simp)
    have hsup : Supply ((varsOf 255).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 255).map obs)
        (show Reach ((varsOf 255).map obs) 0 ((varsOf 255).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    refine ⟨wit, wo, hwMono, by omega, hwEval⟩
  · refine ⟨gates, o, ?_, le_rfl, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
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
inductive btAll {α : Type} (P : α → Prop) : BT α → Prop where
  | empty : btAll P .empty
  | leaf {x : α} : P x → btAll P (.leaf x)
  | node {l r : BT α} : btAll P l → btAll P r → btAll P (.node l r)
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction ht generalizing i with
  | empty => exact hd
  | leaf hx => exact hx
  | node _ _ ihl ihr =>
    unfold btGet
    split
    · exact ihl _
    · exact ihr _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact .leaf hv
  | succ d ih =>
    cases ht with
    | empty =>
      unfold btSet; split
      · exact .node (ih .empty) .empty
      · exact .node .empty (ih .empty)
    | leaf hx =>
      unfold btSet; split
      · exact .node (ih (.leaf hx)) .empty
      · exact .node .empty (ih (.leaf hx))
    | node hl hr =>
      unfold btSet; split
      · exact .node (ih hl) hr
      · exact .node hl (ih hr)
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases ht with
    | leaf hx => exact .leaf (hf _ hx)
    | empty => exact .leaf (hf d0 hd0)
    | node _ _ => exact .leaf (hf d0 hd0)
  | succ d ih =>
    cases ht with
    | empty =>
      unfold btUpdate; split
      · exact .node (ih .empty) .empty
      · exact .node .empty (ih .empty)
    | leaf hx =>
      unfold btUpdate; split
      · exact .node (ih (.leaf hx)) .empty
      · exact .node .empty (ih (.leaf hx))
    | node hl hr =>
      unfold btUpdate; split
      · exact .node (ih hl) hr
      · exact .node hl (ih hr)
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
  exact hgo l (0, BT.empty) h .empty
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL256 ^^^ VAR i else if o.testBit i then VAR i else ALL256
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&&
  fastBitMask z o 6 &&& fastBitMask z o 7
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 8) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL256.testBit r.val = true := by
    simp only [ALL256]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 256 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 256) (ho : o < 256) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 256
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
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 7 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 8) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 8, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 8
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 8
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩, (hbit 7 (by decide)).mp (h 7 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 256 ≤ r := by omega
      have ha : ALL256 < 2^256 := by decide
      have hv : VAR i < 2^256 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^256; decide
      have hlt_m : fastBitMask z o i < 2^256 := by
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
    (hT : T < 2^256)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^256)
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
    have hinv_w : ∀ x : Nat, x < 2^256 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 256
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^256 := by
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
abbrev FastPool := BoundPool × List Nat × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else
    let consts := vals.filter (isConstM c.dom)
    some (c, miss, consts, consts.length)
def fastPoolCut (fp : FastPool) (k a b z : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let consts := fp.2.2.1
  let totC := fp.2.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && consts.contains a then 1 else 0
    let dropB := if !kb && consts.contains b then 1 else 0
    let base := c.lb + (totC - dropA - dropB)
    if k + c.paid >= base + 1 then false
    else
      let m := z &&& c.dom
      if m == 0 || m == c.dom then true
      else if k + c.paid >= base then false
      else
        let okAB := !miss.contains a && !miss.contains b
        if k + c.paid + 1 < base && okAB then true
        else
          let zIn := c.pm.contains m || c.pm.contains (c.dom ^^^ m)
          if zIn then true
          else decide (k + c.paid + 1 < base) && okAB
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
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (hd : d < 4)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 (bin d a.1 b.1) ka kb = true) :
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
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            exact List.Nodup.not_mem_erase (List.Nodup.of_map Prod.fst nd) hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · exact hna' hka (unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa))
        · exact hnb' hkb (unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb))
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      have hlen_f : ((ws.map Prod.fst).filter (isConstM c.dom)).length = (ws.map Prod.fst).countP (isConstM c.dom) := by
        rw [List.countP_eq_length_filter]
      have hca : ((ws.map Prod.fst).filter (isConstM c.dom)).contains a.1 = isConstM c.dom a.1 := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map_of_mem ha, h⟩⟩
      have hcb : ((ws.map Prod.fst).filter (isConstM c.dom)).contains b.1 = isConstM c.dom b.1 := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨List.mem_map_of_mem hb, h⟩⟩
      have hma : (!((ws.map Prod.fst).filter (fun w => !availM c.dom c.pm w)).contains a.1) = availM c.dom c.pm a.1 := by
        cases h : availM c.dom c.pm a.1 <;> simp [List.contains_iff_mem, List.mem_filter, List.mem_map_of_mem ha, h]
      have hmb : (!((ws.map Prod.fst).filter (fun w => !availM c.dom c.pm w)).contains b.1) = availM c.dom c.pm b.1 := by
        cases h : availM c.dom c.pm b.1 <;> simp [List.contains_iff_mem, List.mem_filter, List.mem_map_of_mem hb, h]
      rw [hlen_f, hca, hcb, hma, hmb] at hcut
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut choiceOK
      simp only [choiceVal, h_all_avail, Bool.and_true, List.countP_cons, Bool.and_eq_true, decide_eq_true_eq, hd, true_and]
      rw [hcnt]
      set z := bin d a.1 b.1
      set m := z &&& c.dom
      set restC := (ws.map Prod.fst).countP (isConstM c.dom) - (if !ka && isConstM c.dom a.1 then 1 else 0) - (if !kb && isConstM c.dom b.1 then 1 else 0)
      change (k + c.paid + (!availM c.dom c.pm z).toNat < c.lb + (restC + if isConstM c.dom z then 1 else 0)) ∧
        ((!(!availM c.dom c.pm z)) || (availM c.dom c.pm a.1 && availM c.dom c.pm b.1)) = true
      have hbase_le : ¬(k + c.paid ≥ c.lb + restC + 1) := by
        intro hge; simp only [hge, ↓reduceIte, Bool.false_eq_true] at hcut
      simp only [hbase_le, ↓reduceIte] at hcut
      by_cases hzc : (m == 0 || m == c.dom) = true
      · have hisc : isConstM c.dom z = true := hzc
        have havz : availM c.dom c.pm z = true := by
          unfold availM; dsimp only; rw [show (z &&& c.dom == 0 || z &&& c.dom == c.dom) = true from hzc]; simp
        simp only [hisc, havz, Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or, ite_true, and_true]
        omega
      · have hzc_f : (m == 0 || m == c.dom) = false := Bool.eq_false_iff.mpr hzc
        have hisc : isConstM c.dom z = false := hzc_f
        have hav_eq : availM c.dom c.pm z = (c.pm.contains m || c.pm.contains (c.dom ^^^ m)) := by
          unfold availM; dsimp only
          have hm0 : (m == 0) = false := by cases h1 : (m == 0) <;> simp [h1] at hzc_f ⊢
          have hmd : (m == c.dom) = false := by cases h1 : (m == c.dom) <;> simp [h1] at hzc_f ⊢
          change (m == 0 || m == c.dom || c.pm.contains m || c.pm.contains (c.dom ^^^ m)) = _
          simp [hm0, hmd]
        simp only [hzc_f, Bool.false_eq_true, ↓reduceIte] at hcut
        have hlt_b : ¬(k + c.paid ≥ c.lb + restC) := by
          intro hge; simp only [hge, ↓reduceIte, Bool.false_eq_true] at hcut
        simp only [hlt_b, ↓reduceIte] at hcut
        rw [hav_eq, hisc]
        simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
        by_cases hfast : (k + c.paid + 1 < c.lb + restC ∧ (availM c.dom c.pm a.1 && availM c.dom c.pm b.1) = true)
        · cases hpm : (c.pm.contains m || c.pm.contains (c.dom ^^^ m)) <;>
            simp only [Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false, Bool.true_or, Bool.false_or, hfast.2] <;>
            exact ⟨by omega, trivial⟩
        · have hfast_b : (decide (k + c.paid + 1 < c.lb + restC) && (availM c.dom c.pm a.1 && availM c.dom c.pm b.1)) = false := by
            rw [Bool.eq_false_iff]; intro h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            exact hfast ⟨h.1, (Bool.and_eq_true _ _).mpr h.2⟩
          simp only [hfast_b, Bool.false_eq_true, ↓reduceIte] at hcut
          cases hpm : (c.pm.contains m || c.pm.contains (c.dom ^^^ m))
          · simp only [hpm, Bool.false_eq_true, ↓reduceIte] at hcut
          · simp only [Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.true_or]
            exact ⟨by omega, trivial⟩
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 z.1 ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  if n > cap + 1 then true else
  let z := dbin d a b
  if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
    if n > cap then go false false
    else if n == cap then go false false && go true false && go false true
    else go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^256) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^256)
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
  have hltc : ∀ x ∈ child, x < 2^256 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
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
  dsimp only [z] at hcov_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, Bool.false_eq_true] at test
  dsimp only [dbin] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 (bin d a.1 b.1) ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 _hd ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 (bin d a.1 b.1) ka kb) = false := Bool.eq_false_iff.mpr hfp
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
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^256) (out : T ∉ ws.map Prod.fst)
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
      have hnz_b : (bin d' x.1 y.1 == 0) = false := beq_false_of_ne hnz'
      have hfr_b : (ws.any (fun v => v.1 == bin d' x.1 y.1)) = false := by
        rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
        exact hfr' ((beq_iff_eq.mp heq) ▸ List.mem_map_of_mem hv)
      by_cases hlen : 1 + (ws.length - (if k1 then 0 else 1) - (if k2 then 0 else 1)) > cap
      · unfold evalMoveBT; simp [hlen]
      · unfold testPairBT at ht
        dsimp only [dbin] at ht
        have hnot1 : ¬(ws.length > cap + 1) := by cases k1 <;> cases k2 <;> simp at hlen <;> omega
        simp only [hnot1, ↓reduceIte, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at ht
        by_cases hgt : ws.length > cap
        · simp only [hgt, ↓reduceIte] at ht
          cases k1 <;> cases k2
          · exact ht
          · simp at hlen; omega
          · simp at hlen; omega
          · simp at hlen; omega
        · simp only [hgt, ↓reduceIte] at ht
          by_cases heq : ws.length = cap
          · simp only [heq, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at ht ⊢
            cases k1 <;> cases k2
            · exact ht.1.1
            · exact ht.2
            · exact ht.1.2
            · simp at hlen; omega
          · have hneq : (ws.length == cap) = false := beq_false_of_ne heq
            simp only [hneq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at ht
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
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^256) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^256 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^256)
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
def nodupNats : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupNats xs
lemma nodupNats_sound : ∀ {l : List Nat}, nodupNats l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupNats, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, nodupNats_sound h.2⟩
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
  nodupNats vals && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^256 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^256 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    (nodupNats_sound ok.1.1)
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
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
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
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := .empty
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
def buildPoolsSubBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : BT (Option PoolSpec)) (used : List Nat) : BT (Option BoundPool) :=
  used.foldl (fun acc pIdx =>
    match btGet none pspecs pIdx with
    | none => acc
    | some (slIdx, chIdxs) =>
      match btGet none slices slIdx with
      | none => acc
      | some (dom, lb) =>
        let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
        btSet pdepth acc pIdx (materialize raw cs dom lb)) BT.empty
lemma buildPoolsSubBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))}
    {pspecs : BT (Option PoolSpec)} {used : List Nat}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsSubBT pdepth W raw slices pspecs used) := by
  unfold buildPoolsSubBT
  have hinit : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (BT.empty : BT (Option BoundPool)) := .empty
  generalize (BT.empty : BT (Option BoundPool)) = acc at hinit ⊢
  induction used generalizing acc with
  | nil => exact hinit
  | cons pIdx rest ih =>
    apply ih
    dsimp only
    cases hps : btGet none pspecs pIdx with
    | none => simp only [hps]; exact hinit
    | some spec =>
      cases hsl : btGet none slices spec.1 with
      | none => simp only [hps, hsl]; exact hinit
      | some sl =>
        simp only [hps, hsl]
        apply btAll_set hinit
        intro c hc
        exact materialize_sound (btAll_get (d := none) hSlices (fun _ h => by simp at h) spec.1 sl hsl) hc
lemma checkNodesBT_mem {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k nodes}
    (hT : T < 2^256) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^256) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := by
  intro ns hns
  unfold nodeValsBT; rw [sortNats_toFinset]
  exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
lemma forall_append {α : Type} {P : α → Prop} {l1 l2 : List α}
    (h1 : ∀ x ∈ l1, P x) (h2 : ∀ x ∈ l2, P x) : ∀ x ∈ l1 ++ l2, P x := by
  intro x hx; rcases List.mem_append.mp hx with h | h; exact h1 x h; exact h2 x h
lemma buildBucketsBT_of_mem {W : BT Decor} {T k nodes}
    (hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := .empty
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
lemma obs_all256_xor (G : Nat) : obs (ALL256 ^^^ G) = invW (obs G) := by
  funext r
  have hall : ALL256.testBit r.val = true := by
    simp only [ALL256]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 256 r.val
  simp only [obs, invW, Nat.testBit_xor, hall, Bool.true_xor]

lemma lower_slice_flip {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^256) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^256 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^256) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G ∨ renameW f T = ALL256 ^^^ G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  rcases eq with heq | heq
  · exact lower_slice hT0 hTlt hTb0 hR hG0 hGlt hGb0 f heq covered singles necessary constant L prior
  · classical
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
    have gc : restrictW f (obs T) = invW (obs G) :=
      (obs_renameW f T).symm.trans ((congrArg obs heq).trans (obs_all256_xor G))
    have hnc : ¬Constant (invW (obs G)) := fun hc => obs_not_const hG0 hGlt hGb0 (invW_inv (obs G) ▸ invW_const hc)
    have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (gc ▸ hnc) (restrict_run f (live_to_run run front nd fe))
        (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
    have havG : Avail next (obs G) := by
      rw [gc] at hav; simpa [invW_inv] using avail_inv hav
    have hlo := prior q next hq havG
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
    omega

def liftCheckF (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G || fixWord z o T == ALL256 ^^^ G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL256))

lemma lift_of_f {z o roots T other G essPairs L} (ok : liftCheckF z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheckF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G ∨ renameW (fixRow z o) T = ALL256 ^^^ G := by
    rw [← fixWord_eq_renameW]; exact heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice_flip p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL256]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 256 r'.val |> fun e => by simpa [this] using e⟩

def sliceDirectCheckF (z o : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 256) && decide (o < 256) && ((z &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord z o T == qGoal || fixWord z o T == ALL256 ^^^ qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord z o a))

lemma slice_fast_direct_f {z o raw T qRoots qGoal qL}
    (ok : sliceDirectCheckF z o raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  simp only [sliceDirectCheckF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hz, ho⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  rw [subcubeFast_eq_subcube z o hz ho hzo]
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  rcases heq with heq | heq
  · refine ⟨fixRow z o, qRoots, subcube_fixRow z o hz ho hzo,
      fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
    rw [← obs_renameW, ← fixWord_eq_renameW, heq]
    exact hPrior
  · refine ⟨fixRow z o, qRoots, subcube_fixRow z o hz ho hzo,
      fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← fixWord_eq_renameW, heq, obs_all256_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← fixWord_eq_renameW, heq, obs_all256_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)

def identRow (u v : Nat) (r : Row) : Row :=
  if r.val.testBit u == r.val.testBit v then r
  else ⟨(r.val ^^^ (1 <<< v)) % 256, Nat.mod_lt _ (by decide)⟩

def identDom (u v : Nat) : Nat := ALL256 ^^^ (VAR u ^^^ VAR v)

def identWord (u v w : Nat) : Nat :=
  (List.range 256).foldr (fun r acc =>
    let fr := if r.testBit u == r.testBit v then r else (r ^^^ (1 <<< v)) % 256
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0

lemma identWord_eq_renameW (u v w : Nat) : identWord u v w = renameW (identRow u v) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold identWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 256
  · rw [testBit_renameW (identRow u v) w ⟨r, hr⟩]
    simp only [List.mem_range, hr, decide_true, Bool.true_and, identRow]
    split <;> rfl
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm

lemma identDom_identRow (u v : Nat) (hu : u < 8) (hv : v < 8) (r : Row) :
    (identDom u v).testBit (identRow u v r).val = true := by
  revert r
  interval_cases u <;> interval_cases v <;> decide +kernel

def sliceIdentCheck (u v : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (u < 8) && decide (v < 8) &&
    checkProper qGoal && checkRoots qRoots &&
    (identWord u v T == qGoal || identWord u v T == ALL256 ^^^ qGoal) &&
    raw.all (fun a => freeIn qRoots (identWord u v a))

lemma slice_ident {u v raw T qRoots qGoal qL}
    (ok : sliceIdentCheck u v raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (identDom u v) qL := by
  simp only [sliceIdentCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hu, hv⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  rcases heq with heq | heq
  · refine ⟨identRow u v, qRoots, identDom_identRow u v hu hv,
      fun a ha => freeIn_sound ((identWord_eq_renameW u v a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← identWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
    rw [← obs_renameW, ← identWord_eq_renameW, heq]
    exact hPrior
  · refine ⟨identRow u v, qRoots, identDom_identRow u v hu hv,
      fun a ha => freeIn_sound ((identWord_eq_renameW u v a).symm ▸ hcov a ha),
      by rw [← obs_renameW, ← identWord_eq_renameW, heq, obs_all256_xor]; exact fun hc => obs_not_const g0 glt gb0 (invW_inv (obs qGoal) ▸ invW_const hc), ?_⟩
    rw [← obs_renameW, ← identWord_eq_renameW, heq, obs_all256_xor]
    intro p bank hr hav
    exact hPrior p bank hr (by simpa [invW_inv] using avail_inv hav)


def mkBase (pos neg : List Nat) (rs : List Nat) : List Decor :=
  rs.map fun w => (w, projBits pos w, projBits neg w)
lemma mkBase_ok {pos neg rs} (hR : checkRoots rs = true) :
    ∀ x ∈ mkBase pos neg rs, faithful pos neg x ∧ x.1 < 2^256 := by
  have hr := checkRoots_sound hR
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  exact ⟨⟨rfl, rfl⟩, (hr w hw).1⟩


def g_0 := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def r_0 : List Nat := varsOf 7
def p_0 : List Nat := [3,3,5,5,6,6]
def q_0 : List Nat := [2,1,4,1,4,2]
def F_0 : Nat := fullMask 6
set_option maxHeartbeats 0 in
lemma gp_0 : goodPairs g_0 p_0 q_0 := goodPairs_of (by decide +kernel)
def W_0 : BT Decor := buildWiresBT 2 (mkBase p_0 q_0 r_0) []
lemma W_0_ok : btAll (fun x => faithful p_0 q_0 x ∧ x.1 < 2^256) W_0 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_0 : List (List (Nat × Nat)) := [[]]
def A_0 : BT (List (Nat × Nat)) := btOfList 1 al_0
set_option maxHeartbeats 0 in
lemma A_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_0 = g_0) A_0 := btAll_ofList (autos_of (by decide +kernel))
def S_0 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_0_ok : btAll (fun o => ∀ p, o = some p → Slice r_0 g_0 p.1 p.2) S_0 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_0 : BT (Option PoolSpec) := btOfList 1 ((([] : List PoolSpec)).map some)
def B_0_2 : BT (List (List Nat)) := BT.empty
lemma B_0_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 2 xs.toFinset) B_0_2 := .empty
def P_0_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_0 r_0 S_0 ps_0 []
def N_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_0_3 : checkNodesBT W_0 g_0 F_0 P_0_3 A_0 B_0_2 3 N_0_3 = true := by decide +kernel
def B_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 N_0_3
set_option maxRecDepth 500000 in
lemma B_0_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_0 3 xs.toFinset) B_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok (buildPoolsSubBT_sound S_0_ok) A_0_ok B_0_2_ok C_0_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck r_0 g_0 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT B_0_3 r_0 = true := by decide +kernel
lemma low_0 : Lower r_0 g_0 4 := lower_of_forestBT root_0_ok B_0_3_ok root_0_in
def g_1 := 0xfec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0fec0
def r_1 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_1 : Lower r_1 g_1 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_2 := 0xfffeeac0fffeeac0fffeeac0fffeeac0fffeeac0fffeeac0fffeeac0fffeeac0
def r_2 : List Nat := varsOf 31
def p_2 : List Nat := [6,6,7,7,9,9,11,11,13,13,14,14,17,17,18,18,19,20,20,21,24,24,26,28]
def q_2 : List Nat := [4,2,5,3,8,1,10,3,12,5,12,10,16,1,16,2,3,16,4,5,16,8,10,12]
def F_2 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_2 : goodPairs g_2 p_2 q_2 := goodPairs_of (by decide +kernel)
def W_2 : BT Decor := buildWiresBT 5 (mkBase p_2 q_2 r_2) [(1,2,0),(0,5,4),(1,1,6),(1,2,4),(3,2,4),(1,9,0),(2,10,3),(1,0,1),(1,12,4),(3,3,13),(0,12,4),(1,15,3),(1,3,1),(0,17,4),(1,3,4),(1,0,4),(3,3,20),(1,1,4),(3,3,22),(3,3,4),(1,2,3),(3,25,4),(2,12,4)]
lemma W_2_ok : btAll (fun x => faithful p_2 q_2 x ∧ x.1 < 2^256) W_2 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_2 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1),(2,3)],[(0,2),(1,2),(2,3)],[(0,1),(1,3),(2,3)],[(0,2),(1,3)],[(0,3)],[(0,3),(1,2)]]
def A_2 : BT (List (Nat × Nat)) := btOfList 3 al_2
set_option maxHeartbeats 0 in
lemma A_2_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_2 = g_2) A_2 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_2_0 : Slice r_2 g_2 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0 5 := carry_of (swaps := [(0,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_1 : Slice r_2 g_2 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffaaa00fffaaa00fffaaa00fffaaa00fffaaa00fffaaa00fffaaa00fffaaa00 5 := carry_of (swaps := [(0,1),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_2 : Slice r_2 g_2 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00 5 := carry_of (swaps := [(0,1),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_3 : Slice r_2 g_2 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xfefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_4 : Slice r_2 g_2 (subcubeFast 9 0) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_2_5 : Slice r_2 g_2 (subcubeFast 6 0) 4 := by
  have hc : Lower (varsOf 25) 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00ffaaaa00 4 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 6) (o := 0) (by decide +kernel) hc
def S_2 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5),some (subcubeFast 9 0,4),some (subcubeFast 6 0,4)]
lemma S_2_ok : btAll (fun o => ∀ p, o = some p → Slice r_2 g_2 p.1 p.2) S_2 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_2_0) (forall_cons (fun _ h => by cases h; exact sl_2_1) (forall_cons (fun _ h => by cases h; exact sl_2_2) (forall_cons (fun _ h => by cases h; exact sl_2_3) (forall_cons (fun _ h => by cases h; exact sl_2_4) (forall_cons (fun _ h => by cases h; exact sl_2_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_2 : BT (Option PoolSpec) := btOfList 4 ((([(3,[]),(0,[(3,3,20)]),(0,[(3,3,4)]),(2,[]),(1,[]),(0,[]),(0,[(1,3,1)]),(4,[]),(5,[]),(3,[(1,0,1)])] : List PoolSpec)).map some)
def B_2_2 : BT (List (List Nat)) := BT.empty
lemma B_2_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 2 xs.toFinset) B_2_2 := .empty
def P_2_3 : BT (Option BoundPool) := buildPoolsSubBT 4 W_2 r_2 S_2 ps_2 []
def N_2_3 : List NodeSpec := [([0,7,3,8],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_3 : checkNodesBT W_2 g_2 F_2 P_2_3 A_2 B_2_2 3 N_2_3 = true := by decide +kernel
def B_2_3 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_3
set_option maxRecDepth 500000 in
lemma B_2_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 3 xs.toFinset) B_2_3 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_2_ok C_2_3
def P_2_4 : BT (Option BoundPool) := buildPoolsSubBT 4 W_2 r_2 S_2 ps_2 []
def N_2_4 : List NodeSpec := [([11,0,1,2,4],[],[]),([14,0,1,2,4],[],[]),([0,1,2,16,4],[],[3]),([0,1,2,18,19],[],[2])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_4 : checkNodesBT W_2 g_2 F_2 P_2_4 A_2 B_2_3 4 N_2_4 = true := by decide +kernel
def B_2_4 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_4
set_option maxRecDepth 500000 in
lemma B_2_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 4 xs.toFinset) B_2_4 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_3_ok C_2_4
def P_2_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_2 r_2 S_2 ps_2 [0,1,2,3,4,5,6]
def N_2_5 : List NodeSpec := [([21,0,1,2,4,20],[0,1],[]),([23,0,1,2,3,4],[],[]),([21,0,1,2,4],[],[]),([24,0,1,2,4,19],[0,2],[]),([26,0,1,2,3,4],[],[]),([0,10,1,2,3,4],[0],[0]),([27,0,1,2,3,4],[],[]),([0,1,2,3,4,13],[0,3],[0,2]),([0,1,15,2,3,4],[0,3,4,5],[0,2,4,6]),([0,1,2,17,4,19],[4,6],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_5 : checkNodesBT W_2 g_2 F_2 P_2_5 A_2 B_2_4 5 N_2_5 = true := by decide +kernel
def B_2_5 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_5
set_option maxRecDepth 500000 in
lemma B_2_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 5 xs.toFinset) B_2_5 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_4_ok C_2_5
def P_2_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_2 r_2 S_2 ps_2 [3,4,5,7,8,9]
def N_2_6 : List NodeSpec := [([24,0,1,2,3,4],[3,4,5,7],[0,1,2,4]),([0,1,2,3,4,20],[3,4,5,7],[0,1,2,4,6,7]),([0,1,12,2,3,4],[4,5,7,8,9],[0,4,5,6])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_6 : checkNodesBT W_2 g_2 F_2 P_2_6 A_2 B_2_5 6 N_2_6 = true := by decide +kernel
def B_2_6 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_6
set_option maxRecDepth 500000 in
lemma B_2_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 6 xs.toFinset) B_2_6 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_5_ok C_2_6
def P_2_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_2 r_2 S_2 ps_2 [3,4,5,7,8]
def N_2_7 : List NodeSpec := [([0,1,2,3,4],[3,4,5,7,8],[0,1,2,3,4,5,6])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_2_7 : checkNodesBT W_2 g_2 F_2 P_2_7 A_2 B_2_6 7 N_2_7 = true := by decide +kernel
def B_2_7 : BT (List (List Nat)) := buildBucketsBT W_2 N_2_7
set_option maxRecDepth 500000 in
lemma B_2_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_2 7 xs.toFinset) B_2_7 :=
  buildBucketsBT_sound (by decide) gp_2 W_2_ok (buildPoolsSubBT_sound S_2_ok) A_2_ok B_2_6_ok C_2_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_ok : forestRootCheck r_2 g_2 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_2_in : bucketContainsBT B_2_7 r_2 = true := by decide +kernel
lemma low_2 : Lower r_2 g_2 8 := lower_of_forestBT root_2_ok B_2_7_ok root_2_in
def g_3 := 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8
def r_3 : List Nat := varsOf 15
def p_3 : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12]
def q_3 : List Nat := [2,1,4,1,4,2,8,1,8,2,8,4]
def F_3 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_3 : goodPairs g_3 p_3 q_3 := goodPairs_of (by decide +kernel)
def W_3 : BT Decor := buildWiresBT 4 (mkBase p_3 q_3 r_3) [(1,0,1),(1,4,2),(2,5,3),(1,1,2),(1,3,1),(1,3,2),(2,4,3),(1,3,0)]
lemma W_3_ok : btAll (fun x => faithful p_3 q_3 x ∧ x.1 < 2^256) W_3 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_3 : List (List (Nat × Nat)) := [[],[(2,3)],[(1,2)],[(1,3),(2,3)],[(1,2),(2,3)],[(1,3)],[(0,2),(1,2)],[(0,3),(1,3),(2,3)],[(0,2),(1,2),(2,3)],[(0,3),(1,3)],[(0,1),(1,2)],[(0,2),(1,3)]]
def A_3 : BT (List (Nat × Nat)) := btOfList 4 al_3
set_option maxHeartbeats 0 in
lemma A_3_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_3 = g_3) A_3 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_3_0 : Slice r_3 g_3 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_3_1 : Slice r_3 g_3 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 13) 0xfaa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0faa0 4 := carry_of (swaps := [(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_3_2 : Slice r_3 g_3 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 11) 0xee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88ee88 4 := carry_of (swaps := [(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_3_3 : Slice r_3 g_3 (subcubeFast 8 0) 4 := by
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) low_0
def S_3 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4)]
lemma S_3_ok : btAll (fun o => ∀ p, o = some p → Slice r_3 g_3 p.1 p.2) S_3 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_3_0) (forall_cons (fun _ h => by cases h; exact sl_3_1) (forall_cons (fun _ h => by cases h; exact sl_3_2) (forall_cons (fun _ h => by cases h; exact sl_3_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_3 : BT (Option PoolSpec) := btOfList 2 ((([(2,[]),(1,[]),(3,[]),(0,[])] : List PoolSpec)).map some)
def B_3_2 : BT (List (List Nat)) := BT.empty
lemma B_3_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_3 2 xs.toFinset) B_3_2 := .empty
def P_3_3 : BT (Option BoundPool) := buildPoolsSubBT 2 W_3 r_3 S_3 ps_3 [0,1]
def N_3_3 : List NodeSpec := [([6,0,1,2],[],[]),([0,7,8,9],[0,1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_3_3 : checkNodesBT W_3 g_3 F_3 P_3_3 A_3 B_3_2 3 N_3_3 = true := by decide +kernel
def B_3_3 : BT (List (List Nat)) := buildBucketsBT W_3 N_3_3
set_option maxRecDepth 500000 in
lemma B_3_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_3 3 xs.toFinset) B_3_3 :=
  buildBucketsBT_sound (by decide) gp_3 W_3_ok (buildPoolsSubBT_sound S_3_ok) A_3_ok B_3_2_ok C_3_3
def P_3_4 : BT (Option BoundPool) := buildPoolsSubBT 2 W_3 r_3 S_3 ps_3 [1,2,3]
def N_3_4 : List NodeSpec := [([0,1,2,5,3],[2],[0]),([10,0,1,2,3],[],[]),([0,1,2,11,8],[1,3],[10])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_3_4 : checkNodesBT W_3 g_3 F_3 P_3_4 A_3 B_3_3 4 N_3_4 = true := by decide +kernel
def B_3_4 : BT (List (List Nat)) := buildBucketsBT W_3 N_3_4
set_option maxRecDepth 500000 in
lemma B_3_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_3 4 xs.toFinset) B_3_4 :=
  buildBucketsBT_sound (by decide) gp_3 W_3_ok (buildPoolsSubBT_sound S_3_ok) A_3_ok B_3_3_ok C_3_4
def P_3_5 : BT (Option BoundPool) := buildPoolsSubBT 2 W_3 r_3 S_3 ps_3 [0,1,2,3]
def N_3_5 : List NodeSpec := [([0,1,4,2,3],[0,1,2,3],[0,1,3,5,7,9])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_3_5 : checkNodesBT W_3 g_3 F_3 P_3_5 A_3 B_3_4 5 N_3_5 = true := by decide +kernel
def B_3_5 : BT (List (List Nat)) := buildBucketsBT W_3 N_3_5
set_option maxRecDepth 500000 in
lemma B_3_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_3 5 xs.toFinset) B_3_5 :=
  buildBucketsBT_sound (by decide) gp_3 W_3_ok (buildPoolsSubBT_sound S_3_ok) A_3_ok B_3_4_ok C_3_5
def P_3_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_3 r_3 S_3 ps_3 [0,1,2,3]
def N_3_6 : List NodeSpec := [([0,1,2,3],[0,1,2,3],[0,2,4,6,8,11])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_3_6 : checkNodesBT W_3 g_3 F_3 P_3_6 A_3 B_3_5 6 N_3_6 = true := by decide +kernel
def B_3_6 : BT (List (List Nat)) := buildBucketsBT W_3 N_3_6
set_option maxRecDepth 500000 in
lemma B_3_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_3 6 xs.toFinset) B_3_6 :=
  buildBucketsBT_sound (by decide) gp_3 W_3_ok (buildPoolsSubBT_sound S_3_ok) A_3_ok B_3_5_ok C_3_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_3_ok : forestRootCheck r_3 g_3 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_3_in : bucketContainsBT B_3_6 r_3 = true := by decide +kernel
lemma low_3 : Lower r_3 g_3 7 := lower_of_forestBT root_3_ok B_3_6_ok root_3_in
def g_4 := 0xfffefec0fffefec0fffefec0fffefec0fffefec0fffefec0fffefec0fffefec0
def r_4 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_4 : Lower r_4 g_4 8 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_5 := 0xfee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0fee0
def r_5 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_5 : Lower r_5 g_5 5 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_6 := 0xffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8ffe8
def r_6 : List Nat := varsOf 15
set_option maxHeartbeats 0 in
lemma low_6 : Lower r_6 g_6 5 := lift_of_f (z := 8) (o := 0) (other := r_0) (G := g_0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) low_0
def g_7 := 0xfac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0fac0
def r_7 : List Nat := varsOf 15
def p_7 : List Nat := [6,6,7,7,9,9,11,11,12,12,13,14]
def q_7 : List Nat := [4,2,5,3,8,1,10,3,8,4,5,10]
def F_7 : Nat := fullMask 12
set_option maxHeartbeats 0 in
lemma gp_7 : goodPairs g_7 p_7 q_7 := goodPairs_of (by decide +kernel)
def W_7 : BT Decor := buildWiresBT 2 (mkBase p_7 q_7 r_7) []
lemma W_7_ok : btAll (fun x => faithful p_7 q_7 x ∧ x.1 < 2^256) W_7 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_7 : List (List (Nat × Nat)) := [[]]
def A_7 : BT (List (Nat × Nat)) := btOfList 1 al_7
set_option maxHeartbeats 0 in
lemma A_7_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_7 = g_7) A_7 := btAll_ofList (autos_of (by decide +kernel))
def S_7 : BT (Option (Nat × Nat)) := btOfList 1 []
lemma S_7_ok : btAll (fun o => ∀ p, o = some p → Slice r_7 g_7 p.1 p.2) S_7 := btAll_ofList (fun _ h => (List.not_mem_nil h).elim)
def ps_7 : BT (Option PoolSpec) := btOfList 1 ((([] : List PoolSpec)).map some)
def B_7_2 : BT (List (List Nat)) := BT.empty
lemma B_7_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 2 xs.toFinset) B_7_2 := .empty
def P_7_3 : BT (Option BoundPool) := buildPoolsSubBT 1 W_7 r_7 S_7 ps_7 []
def N_7_3 : List NodeSpec := [([0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_7_3 : checkNodesBT W_7 g_7 F_7 P_7_3 A_7 B_7_2 3 N_7_3 = true := by decide +kernel
def B_7_3 : BT (List (List Nat)) := buildBucketsBT W_7 N_7_3
set_option maxRecDepth 500000 in
lemma B_7_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_7 3 xs.toFinset) B_7_3 :=
  buildBucketsBT_sound (by decide) gp_7 W_7_ok (buildPoolsSubBT_sound S_7_ok) A_7_ok B_7_2_ok C_7_3
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_ok : forestRootCheck r_7 g_7 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_7_in : bucketContainsBT B_7_3 r_7 = true := by decide +kernel
lemma low_7 : Lower r_7 g_7 4 := lower_of_forestBT root_7_ok B_7_3_ok root_7_in
def g_8 := 0xfffafcc0fffafcc0fffafcc0fffafcc0fffafcc0fffafcc0fffafcc0fffafcc0
def r_8 : List Nat := varsOf 31
def p_8 : List Nat := [6,6,7,7,10,10,11,11,12,12,13,13,17,17,19,19,20,20,21,22,24,24,25,26]
def q_8 : List Nat := [4,2,5,3,8,2,9,3,8,4,9,5,16,1,18,3,16,4,5,18,16,8,9,18]
def F_8 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_8 : goodPairs g_8 p_8 q_8 := goodPairs_of (by decide +kernel)
def W_8 : BT Decor := buildWiresBT 3 (mkBase p_8 q_8 r_8) [(1,2,3),(3,1,5)]
lemma W_8_ok : btAll (fun x => faithful p_8 q_8 x ∧ x.1 < 2^256) W_8 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_8 : List (List (Nat × Nat)) := [[]]
def A_8 : BT (List (Nat × Nat)) := btOfList 1 al_8
set_option maxHeartbeats 0 in
lemma A_8_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_8 = g_8) A_8 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_8_0 : Slice r_8 g_8 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0fff0fcc0 5 := carry_of (swaps := [(0,4),(1,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_1 : Slice r_8 g_8 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_2 : Slice r_8 g_8 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000fffaf000 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_3 : Slice r_8 g_8 (subcubeFast 17 0) 4 := by
  have hc : Lower (varsOf 14) 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0 4 := carry_of (swaps := [(0,3),(1,3),(2,3)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 17) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_4 : Slice r_8 g_8 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 27) 0xffaacc00ffaacc00ffaacc00ffaacc00ffaacc00ffaacc00ffaacc00ffaacc00 4 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_8_5 : Slice r_8 g_8 (subcubeFast 8 0) 4 := by
  have hc : Lower (varsOf 23) 0xfafac0c0fafac0c0fafac0c0fafac0c0fafac0c0fafac0c0fafac0c0fafac0c0 4 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
def S_8 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 17 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4)]
lemma S_8_ok : btAll (fun o => ∀ p, o = some p → Slice r_8 g_8 p.1 p.2) S_8 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_8_0) (forall_cons (fun _ h => by cases h; exact sl_8_1) (forall_cons (fun _ h => by cases h; exact sl_8_2) (forall_cons (fun _ h => by cases h; exact sl_8_3) (forall_cons (fun _ h => by cases h; exact sl_8_4) (forall_cons (fun _ h => by cases h; exact sl_8_5) (fun _ h => (List.not_mem_nil h).elim)))))))
def ps_8 : BT (Option PoolSpec) := btOfList 3 ((([(1,[]),(0,[]),(2,[]),(4,[]),(3,[]),(5,[])] : List PoolSpec)).map some)
def B_8_3 : BT (List (List Nat)) := BT.empty
lemma B_8_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 3 xs.toFinset) B_8_3 := .empty
def P_8_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_8 r_8 S_8 ps_8 []
def N_8_4 : List NodeSpec := [([6,0,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_4 : checkNodesBT W_8 g_8 F_8 P_8_4 A_8 B_8_3 4 N_8_4 = true := by decide +kernel
def B_8_4 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_4
set_option maxRecDepth 500000 in
lemma B_8_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 4 xs.toFinset) B_8_4 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_3_ok C_8_4
def P_8_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_8 r_8 S_8 ps_8 [0,1,2,3]
def N_8_5 : List NodeSpec := [([0,1,2,3,5,4],[0,1,2,3],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_5 : checkNodesBT W_8 g_8 F_8 P_8_5 A_8 B_8_4 5 N_8_5 = true := by decide +kernel
def B_8_5 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_5
set_option maxRecDepth 500000 in
lemma B_8_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 5 xs.toFinset) B_8_5 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_4_ok C_8_5
def P_8_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_8 r_8 S_8 ps_8 [0,1,2,3,4,5]
def N_8_6 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_8_6 : checkNodesBT W_8 g_8 F_8 P_8_6 A_8 B_8_5 6 N_8_6 = true := by decide +kernel
def B_8_6 : BT (List (List Nat)) := buildBucketsBT W_8 N_8_6
set_option maxRecDepth 500000 in
lemma B_8_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_8 6 xs.toFinset) B_8_6 :=
  buildBucketsBT_sound (by decide) gp_8 W_8_ok (buildPoolsSubBT_sound S_8_ok) A_8_ok B_8_5_ok C_8_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_8_ok : forestRootCheck r_8 g_8 [(VAR 0,16,17),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,2,10),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_8_in : bucketContainsBT B_8_6 r_8 = true := by decide +kernel
lemma low_8 : Lower r_8 g_8 7 := lower_of_forestBT root_8_ok B_8_6_ok root_8_in
def g_9 := 0xfffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0fffceac0
def r_9 : List Nat := varsOf 31
def p_9 : List Nat := [6,6,7,7,9,9,11,11,13,13,14,14,18,18,19,19,20,20,21,21,24,24,25,26,28]
def q_9 : List Nat := [4,2,5,3,8,1,10,3,12,5,12,10,16,2,17,3,16,4,17,5,16,8,17,10,12]
def F_9 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_9 : goodPairs g_9 p_9 q_9 := goodPairs_of (by decide +kernel)
def W_9 : BT Decor := buildWiresBT 4 (mkBase p_9 q_9 r_9) [(1,1,4),(3,2,5),(3,2,4),(1,1,2)]
lemma W_9_ok : btAll (fun x => faithful p_9 q_9 x ∧ x.1 < 2^256) W_9 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_9 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_9 : BT (List (Nat × Nat)) := btOfList 1 al_9
set_option maxHeartbeats 0 in
lemma A_9_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_9 = g_9) A_9 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_9_0 : Slice r_9 g_9 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0 5 := carry_of (swaps := [(0,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_1 : Slice r_9 g_9 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 30) 0xfffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0fffcffc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_6
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_2 : Slice r_9 g_9 (subcubeFast 9 0) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 9) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_3 : Slice r_9 g_9 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 29) 0xfff0aa00fff0aa00fff0aa00fff0aa00fff0aa00fff0aa00fff0aa00fff0aa00 4 := carry_of (swaps := [(1,4),(2,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_9_4 : Slice r_9 g_9 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 27) 0xffccaa00ffccaa00ffccaa00ffccaa00ffccaa00ffccaa00ffccaa00ffccaa00 4 := carry_of (swaps := [(2,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
def S_9 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,5),some (subcubeFast 0 1,5),some (subcubeFast 9 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4)]
lemma S_9_ok : btAll (fun o => ∀ p, o = some p → Slice r_9 g_9 p.1 p.2) S_9 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_9_0) (forall_cons (fun _ h => by cases h; exact sl_9_1) (forall_cons (fun _ h => by cases h; exact sl_9_2) (forall_cons (fun _ h => by cases h; exact sl_9_3) (forall_cons (fun _ h => by cases h; exact sl_9_4) (fun _ h => (List.not_mem_nil h).elim))))))
def ps_9 : BT (Option PoolSpec) := btOfList 3 ((([(1,[]),(0,[]),(4,[]),(3,[]),(2,[])] : List PoolSpec)).map some)
def B_9_3 : BT (List (List Nat)) := BT.empty
lemma B_9_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 3 xs.toFinset) B_9_3 := .empty
def P_9_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_9 r_9 S_9 ps_9 []
def N_9_4 : List NodeSpec := [([6,0,1,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_4 : checkNodesBT W_9 g_9 F_9 P_9_4 A_9 B_9_3 4 N_9_4 = true := by decide +kernel
def B_9_4 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_4
set_option maxRecDepth 500000 in
lemma B_9_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 4 xs.toFinset) B_9_4 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_3_ok C_9_4
def P_9_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_9 r_9 S_9 ps_9 [0,1,2,3]
def N_9_5 : List NodeSpec := [([7,0,1,2,3,4],[0,1,2],[]),([0,1,2,3,4,5],[2,3],[0]),([0,1,2,8,3,4],[3],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_5 : checkNodesBT W_9 g_9 F_9 P_9_5 A_9 B_9_4 5 N_9_5 = true := by decide +kernel
def B_9_5 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_5
set_option maxRecDepth 500000 in
lemma B_9_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 5 xs.toFinset) B_9_5 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_4_ok C_9_5
def P_9_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_9 r_9 S_9 ps_9 [0,1,2,3,4]
def N_9_6 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_9_6 : checkNodesBT W_9 g_9 F_9 P_9_6 A_9 B_9_5 6 N_9_6 = true := by decide +kernel
def B_9_6 : BT (List (List Nat)) := buildBucketsBT W_9 N_9_6
set_option maxRecDepth 500000 in
lemma B_9_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_9 6 xs.toFinset) B_9_6 :=
  buildBucketsBT_sound (by decide) gp_9 W_9_ok (buildPoolsSubBT_sound S_9_ok) A_9_ok B_9_5_ok C_9_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_ok : forestRootCheck r_9 g_9 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9),(VAR 4,2,18)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_9_in : bucketContainsBT B_9_6 r_9 = true := by decide +kernel
lemma low_9 : Lower r_9 g_9 7 := lower_of_forestBT root_9_ok B_9_6_ok root_9_in
def g_10 := 0xffffffeefff8f888ffffffeefff8f888ffffffeefff8f888ffffffeefff8f888
def r_10 : List Nat := varsOf 63
def p_10 : List Nat := [3,3,7,7,11,11,12,12,13,13,14,14,19,19,20,20,21,21,22,22,24,24,25,25,26,26,33,33,34,34,37,37,38,38,40,40,41,42,44,48,48,49,50,52]
def q_10 : List Nat := [2,1,6,5,10,9,8,4,9,5,10,6,18,17,16,4,17,5,18,6,16,8,17,9,18,10,32,1,32,2,36,5,36,6,32,8,9,10,36,32,16,17,18,36]
def F_10 : Nat := fullMask 44
set_option maxHeartbeats 0 in
lemma gp_10 : goodPairs g_10 p_10 q_10 := goodPairs_of (by decide +kernel)
def W_10 : BT Decor := buildWiresBT 5 (mkBase p_10 q_10 r_10) [(1,3,5),(3,4,6),(1,4,5),(3,3,8),(1,3,4),(3,2,10),(3,1,5),(1,11,12),(1,0,5),(3,1,14),(1,0,1),(1,12,3),(1,17,4),(1,11,5),(1,12,4),(2,17,4),(1,10,5),(3,4,5),(1,23,3),(1,2,5),(1,0,3),(2,26,4)]
lemma W_10_ok : btAll (fun x => faithful p_10 q_10 x ∧ x.1 < 2^256) W_10 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_10 : List (List (Nat × Nat)) := [[],[(3,4)],[(0,1)],[(0,1),(3,4)]]
def A_10 : BT (List (Nat × Nat)) := btOfList 2 al_10
set_option maxHeartbeats 0 in
lemma A_10_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_10 = g_10) A_10 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_10_0 : Slice r_10 g_10 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) 0xffffffeeff888888ffffffeeff888888ffffffeeff888888ffffffeeff888888 8 := carry_of (swaps := [(1,3),(2,5),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_1 : Slice r_10 g_10 (identDom 0 2) 8 := by
  have hc : Lower (varsOf 59) 0xffffffeeffaaaa88ffffffeeffaaaa88ffffffeeffaaaa88ffffffeeffaaaa88 8 := carry_of (swaps := [(0,3),(1,3),(2,5),(4,5)]) (by decide +kernel) low_4
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_2 : Slice r_10 g_10 (subcubeFast 1 0) 7 := by
  have hc : Lower (varsOf 62) 0xffffffccfff0f000ffffffccfff0f000ffffffccfff0f000ffffffccfff0f000 7 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_3 : Slice r_10 g_10 (subcubeFast 2 0) 7 := by
  have hc : Lower (varsOf 61) 0xffffffaafff0f000ffffffaafff0f000ffffffaafff0f000ffffffaafff0f000 7 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_4 : Slice r_10 g_10 (subcubeFast 8 0) 7 := by
  have hc : Lower (varsOf 55) 0xffffeeeef8f88888ffffeeeef8f88888ffffeeeef8f88888ffffeeeef8f88888 7 := carry_of (swaps := [(0,1),(1,2),(3,5),(4,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_5 : Slice r_10 g_10 (subcubeFast 16 0) 7 := by
  have hc : Lower (varsOf 47) 0xffeeffeef888f888ffeeffeef888f888ffeeffeef888f888ffeeffeef888f888 7 := carry_of (swaps := [(0,1),(1,2),(4,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_6 : Slice r_10 g_10 (identDom 2 5) 8 := by
  have hc : Lower (varsOf 31) 0xfff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8fff8f8e8 8 := carry_of (swaps := [(1,3),(2,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_7 : Slice r_10 g_10 (subcubeFast 7 0) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000ffffff00ff000000ffffff00ff000000ffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 7) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_8 : Slice r_10 g_10 (subcubeFast 35 0) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 35) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_9 : Slice r_10 g_10 (subcubeFast 34 1) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 34) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_10 : Slice r_10 g_10 (subcubeFast 33 2) 4 := by
  have hc : Lower (varsOf 28) 0xfff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000fff0f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 33) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_11 : Slice r_10 g_10 (subcubeFast 28 0) 4 := by
  have hc : Lower (varsOf 35) 0xeeeeeeee88888888eeeeeeee88888888eeeeeeee88888888eeeeeeee88888888 4 := carry_of (swaps := [(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 28) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_10_12 : Slice r_10 g_10 (subcubeFast 24 4) 4 := by
  have hc : Lower (varsOf 35) 0xeeeeeeee88888888eeeeeeee88888888eeeeeeee88888888eeeeeeee88888888 4 := carry_of (swaps := [(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 24) (o := 4) (by decide +kernel) hc
def S_10 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 4 0,8),some (identDom 0 2,8),some (subcubeFast 1 0,7),some (subcubeFast 2 0,7),some (subcubeFast 8 0,7),some (subcubeFast 16 0,7),some (identDom 2 5,8),some (subcubeFast 7 0,4),some (subcubeFast 35 0,4),some (subcubeFast 34 1,4),some (subcubeFast 33 2,4),some (subcubeFast 28 0,4),some (subcubeFast 24 4,4)]
lemma S_10_ok : btAll (fun o => ∀ p, o = some p → Slice r_10 g_10 p.1 p.2) S_10 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_10_0) (forall_cons (fun _ h => by cases h; exact sl_10_1) (forall_cons (fun _ h => by cases h; exact sl_10_2) (forall_cons (fun _ h => by cases h; exact sl_10_3) (forall_cons (fun _ h => by cases h; exact sl_10_4) (forall_cons (fun _ h => by cases h; exact sl_10_5) (forall_cons (fun _ h => by cases h; exact sl_10_6) (forall_cons (fun _ h => by cases h; exact sl_10_7) (forall_cons (fun _ h => by cases h; exact sl_10_8) (forall_cons (fun _ h => by cases h; exact sl_10_9) (forall_cons (fun _ h => by cases h; exact sl_10_10) (forall_cons (fun _ h => by cases h; exact sl_10_11) (forall_cons (fun _ h => by cases h; exact sl_10_12) (fun _ h => (List.not_mem_nil h).elim))))))))))))))
def ps_10 : BT (Option PoolSpec) := btOfList 6 ((([(12,[]),(5,[]),(2,[(1,3,4),(3,2,10)]),(0,[]),(9,[]),(10,[]),(0,[(1,4,3),(1,4,5),(1,3,5)]),(11,[]),(0,[(1,0,5),(3,1,14)]),(4,[(1,0,5),(3,1,14)]),(3,[(1,3,4),(3,2,10)]),(4,[]),(0,[(1,4,3),(1,10,5),(3,4,22)]),(8,[]),(0,[(3,4,5),(1,23,3)]),(2,[]),(0,[(1,3,5),(3,4,6)]),(5,[(1,3,5)]),(0,[(1,3,5)]),(6,[(1,3,5)]),(0,[(1,3,5),(1,4,5)]),(2,[(1,3,4)]),(7,[]),(4,[(1,0,1)]),(2,[(1,2,5),(1,3,5)]),(4,[(1,2,5)]),(0,[(1,3,4),(1,10,5)]),(1,[(1,3,4),(3,2,10)]),(2,[(2,26,4)]),(3,[]),(0,[(1,0,3),(2,26,4)]),(4,[(2,26,4)]),(2,[(3,1,14)]),(5,[(1,0,5),(3,1,14)]),(3,[(1,3,4)]),(0,[(1,0,5)]),(4,[(1,0,5)]),(2,[(3,1,5),(1,12,3)]),(0,[(3,1,5),(1,12,3)]),(4,[(3,1,5)]),(6,[(1,3,4)]),(0,[(1,3,4)]),(0,[(3,1,5)]),(2,[(1,2,5),(3,4,5)]),(0,[(1,4,3),(1,4,5)]),(4,[(1,4,5)]),(2,[(3,4,5)]),(6,[]),(0,[(3,4,5)]),(2,[(1,3,5)]),(2,[(1,2,5)]),(2,[(3,1,5)]),(5,[(3,1,5)]),(5,[(1,0,5)]),(3,[(1,0,3)]),(0,[(1,0,3)]),(0,[(1,0,1)]),(5,[(1,0,1)])] : List PoolSpec)).map some)
def B_10_4 : BT (List (List Nat)) := BT.empty
lemma B_10_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 4 xs.toFinset) B_10_4 := .empty
def P_10_5 : BT (Option BoundPool) := buildPoolsSubBT 6 W_10 r_10 S_10 ps_10 [0]
def N_10_5 : List NodeSpec := [([7,9,0,1,2,5],[0],[]),([13,0,1,3,4,5],[],[]),([11,15,0,3,4,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_5 : checkNodesBT W_10 g_10 F_10 P_10_5 A_10 B_10_4 5 N_10_5 = true := by decide +kernel
def B_10_5 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_5
set_option maxRecDepth 500000 in
lemma B_10_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 5 xs.toFinset) B_10_5 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_4_ok C_10_5
def P_10_6 : BT (Option BoundPool) := buildPoolsSubBT 6 W_10 r_10 S_10 ps_10 [0,1,2,3,4,5,6,7,8,9,10,11,12,13]
def N_10_6 : List NodeSpec := [([7,0,1,2,3,5,8],[0,1],[0]),([11,0,1,16,3,4,5],[2],[]),([0,1,2,3,4,18,5],[0,3],[]),([0,1,2,10,6,8],[4,5,6,7],[]),([15,0,2,3,4,10,5],[8,9],[0]),([11,12,0,1,3,4,5],[7,10],[0]),([0,1,3,4,5,19],[7],[]),([11,0,1,3,4,5,14],[2,10],[0]),([0,1,2,3,20,10,5],[11],[]),([21,0,1,2,3,4,5],[],[]),([7,0,1,2,3,5,22],[0,3,12],[0]),([0,1,2,10,5,6,8],[0,6,13],[]),([7,0,1,2,10,5,6],[0,1,11],[]),([7,0,1,2,3,6,8],[1,13],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_6 : checkNodesBT W_10 g_10 F_10 P_10_6 A_10 B_10_5 6 N_10_6 = true := by decide +kernel
def B_10_6 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_6
set_option maxRecDepth 500000 in
lemma B_10_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 6 xs.toFinset) B_10_6 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_5_ok C_10_6
def P_10_7 : BT (Option BoundPool) := buildPoolsSubBT 6 W_10 r_10 S_10 ps_10 [0,1,2,3,4,5,7,8,9,10,11,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45]
def N_10_7 : List NodeSpec := [([0,1,2,3,24,4,5],[0,3,13,14],[]),([7,0,1,2,3,4,5,6],[0,1,11,13],[0]),([7,0,1,2,3,4,5],[0,3,4,5,11,15,16,17],[0]),([0,1,2,3,4,5,6,22],[0,18],[0,1]),([23,0,1,2,3,4,6],[7,11,13,17,19],[]),([0,1,2,3,4,5,6,8],[0,13,20],[0,1]),([0,1,16,2,3,4,10,5],[4,21,22,23],[0]),([0,1,3,4,25,6],[0,4,5,13,24,25],[]),([0,1,2,3,4,5,22],[0,4,5,15,26],[0,1]),([0,1,3,4,5,25,6],[0,13],[]),([11,0,1,3,4,5],[2,7,10,27],[0,2]),([27,0,1,2,3,4,5],[3,4,11,15,28,29,30,31],[]),([15,0,2,3,4,5],[8,9,13,32,33],[0]),([0,1,2,3,4,10,5,14],[4,13,15,21,34,35,36],[0]),([0,1,2,3,17,4,5],[1,3,13,37,38,39],[0,1]),([12,0,1,2,3,4,10,5],[1,7,11,13,34,39,40,41,42],[0,1]),([23,0,1,3,4,25],[0,13,43],[]),([0,1,2,3,10,5,8],[0,4,5,7,44],[0,1]),([0,1,2,3,4,6,8],[4,5,17,20,45],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_7 : checkNodesBT W_10 g_10 F_10 P_10_7 A_10 B_10_6 7 N_10_7 = true := by decide +kernel
def B_10_7 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_7
set_option maxRecDepth 500000 in
lemma B_10_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 7 xs.toFinset) B_10_7 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_6_ok C_10_7
def P_10_8 : BT (Option BoundPool) := buildPoolsSubBT 6 W_10 r_10 S_10 ps_10 [0,1,3,4,5,7,11,13,15,17,18,21,23,25,29,34,35,36,39,41,42,46,47,48,49,50,51,52,53,54,55,56,57]
def N_10_8 : List NodeSpec := [([23,0,1,2,3,4,5],[1,3,11,13,15,46,47,48],[0]),([0,1,2,3,4,5,6],[4,5,11,13,17,18,49],[0,1]),([0,1,2,3,4,10,5],[0,1,4,5,7,11,21,34,41],[0,1,2]),([0,1,3,4,5,25],[0,3,4,5,13,25,50],[0,1]),([12,0,1,2,3,4,5],[1,3,11,13,15,29,39,42,47,51,52],[0,1]),([0,1,2,3,4,5,14],[4,13,15,29,35,36,53],[0]),([0,1,2,3,26,4,5],[1,4,11,15,54,55],[0]),([0,1,16,2,3,4,5],[4,13,15,23,29,56,57],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_8 : checkNodesBT W_10 g_10 F_10 P_10_8 A_10 B_10_7 8 N_10_8 = true := by decide +kernel
def B_10_8 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_8
set_option maxRecDepth 500000 in
lemma B_10_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 8 xs.toFinset) B_10_8 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_7_ok C_10_8
def P_10_9 : BT (Option BoundPool) := buildPoolsSubBT 6 W_10 r_10 S_10 ps_10 [1,3,11,15,29]
def N_10_9 : List NodeSpec := [([0,1,2,3,4,5],[1,3,11,15,29],[0,1,2,3])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_10_9 : checkNodesBT W_10 g_10 F_10 P_10_9 A_10 B_10_8 9 N_10_9 = true := by decide +kernel
def B_10_9 : BT (List (List Nat)) := buildBucketsBT W_10 N_10_9
set_option maxRecDepth 500000 in
lemma B_10_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_10 9 xs.toFinset) B_10_9 :=
  buildBucketsBT_sound (by decide) gp_10 W_10_ok (buildPoolsSubBT_sound S_10_ok) A_10_ok B_10_8_ok C_10_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_ok : forestRootCheck r_10 g_10 [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,4,20),(VAR 5,1,33)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_10_in : bucketContainsBT B_10_9 r_10 = true := by decide +kernel
lemma low_10 : Lower r_10 g_10 10 := lower_of_forestBT root_10_ok B_10_9_ok root_10_in
def g_11 := 0xfffffffeffffffeefffffefafff0cc00fffffffeffffffeefffffefafff0cc00
def r_11 : List Nat := varsOf 127
set_option maxHeartbeats 0 in
lemma low_11 : Lower r_11 g_11 11 := by
  have hc : Lower (varsOf 126) 0xfffffffcffffffccfffffcf0fff0cc00fffffffcffffffccfffffcf0fff0cc00 10 := carry_of (swaps := [(0,6),(1,2),(2,6),(4,5),(5,6)]) (by decide +kernel) low_10
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,32,33)]) (by decide +kernel) hc
def g_12 := 0xfffffffefffffffefffefffcfeeef000fffffffefffffffefffefffcfeeef000
def r_12 : List Nat := varsOf 127
set_option maxHeartbeats 0 in
lemma low_12 : Lower r_12 g_12 11 := by
  have hc : Lower (varsOf 125) 0xfffffffafffffffafffafff0faaaf000fffffffafffffffafffafff0faaaf000 10 := carry_of (swaps := [(1,6),(2,3),(3,4),(4,6),(5,6)]) (by decide +kernel) low_10
  exact lift_of_f (z := 2) (o := 0) (essPairs := [(VAR 1,16,18)]) (by decide +kernel) hc
def g_13 := 0xffffffeefefafc00ffffffeefefafc00ffffffeefefafc00ffffffeefefafc00
def r_13 : List Nat := varsOf 63
set_option maxHeartbeats 0 in
lemma low_13 : Lower r_13 g_13 9 := by
  have hc : Lower (varsOf 59) 0xffffffeeeeaacc00ffffffeeeeaacc00ffffffeeeeaacc00ffffffeeeeaacc00 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_2
  exact lift_of_f (z := 4) (o := 0) (essPairs := [(VAR 2,8,12)]) (by decide +kernel) hc
def g_14 := 0xfffffffefeeef000fffffffefeeef000fffffffefeeef000fffffffefeeef000
def r_14 : List Nat := varsOf 63
set_option maxHeartbeats 0 in
lemma low_14 : Lower r_14 g_14 9 := by
  have hc : Lower (varsOf 62) 0xfffffffcfcccf000fffffffcfcccf000fffffffcfcccf000fffffffcfcccf000 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_2
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_15 := 0xfffffffcfeeef000fffffffcfeeef000fffffffcfeeef000fffffffcfeeef000
def r_15 : List Nat := varsOf 63
set_option maxHeartbeats 0 in
lemma low_15 : Lower r_15 g_15 9 := by
  have hc : Lower (varsOf 62) 0xfffffffcfcccf000fffffffcfcccf000fffffffcfcccf000fffffffcfcccf000 8 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_2
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_16 := 0xfffefc00fffefc00fffefc00fffefc00fffefc00fffefc00fffefc00fffefc00
def r_16 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_16 : Lower r_16 g_16 6 := by
  have hc : Lower (varsOf 30) 0xfffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00fffcfc00 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_17 := 0xffffffe8ffffffe8ffffffe8ffffffe8ffffffe8ffffffe8ffffffe8ffffffe8
def r_17 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_17 : Lower r_17 g_17 6 := by
  have hc : Lower (varsOf 23) 0xffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8ffffe8e8 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_6
  exact lift_of_f (z := 8) (o := 0) (essPairs := [(VAR 3,0,8)]) (by decide +kernel) hc
def g_18 := 0xffeefac0ffeefac0ffeefac0ffeefac0ffeefac0ffeefac0ffeefac0ffeefac0
def r_18 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_18 : Lower r_18 g_18 6 := by
  have hc : Lower (varsOf 29) 0xffaafa00ffaafa00ffaafa00ffaafa00ffaafa00ffaafa00ffaafa00ffaafa00 5 := carry_of (swaps := [(0,1),(1,4),(2,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 2) (o := 0) (essPairs := [(VAR 1,4,6)]) (by decide +kernel) hc
def g_19 := 0xfffefac0fffefac0fffefac0fffefac0fffefac0fffefac0fffefac0fffefac0
def r_19 : List Nat := varsOf 31
def p_19 : List Nat := [6,6,7,7,9,9,11,11,12,12,13,14,17,17,18,18,19,20,20,21,24,24,26]
def q_19 : List Nat := [4,2,5,3,8,1,10,3,8,4,5,10,16,1,16,2,3,16,4,5,16,8,10]
def F_19 : Nat := fullMask 23
set_option maxHeartbeats 0 in
lemma gp_19 : goodPairs g_19 p_19 q_19 := goodPairs_of (by decide +kernel)
def W_19 : BT Decor := buildWiresBT 3 (mkBase p_19 q_19 r_19) []
lemma W_19_ok : btAll (fun x => faithful p_19 q_19 x ∧ x.1 < 2^256) W_19 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_19 : List (List (Nat × Nat)) := [[]]
def A_19 : BT (List (Nat × Nat)) := btOfList 1 al_19
set_option maxHeartbeats 0 in
lemma A_19_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_19 = g_19) A_19 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_19_0 : Slice r_19 g_19 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcf0c0fffcf0c0fffcf0c0fffcf0c0fffcf0c0fffcf0c0fffcf0c0fffcf0c0 5 := carry_of (swaps := [(0,4),(1,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_1 : Slice r_19 g_19 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffafa00fffafa00fffafa00fffafa00fffafa00fffafa00fffafa00fffafa00 5 := carry_of (swaps := [(1,4),(2,4),(3,4)]) (by decide +kernel) low_5
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_2 : Slice r_19 g_19 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00 5 := carry_of (swaps := [(0,1),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_19_3 : Slice r_19 g_19 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xfefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
def S_19 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5)]
lemma S_19_ok : btAll (fun o => ∀ p, o = some p → Slice r_19 g_19 p.1 p.2) S_19 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_19_0) (forall_cons (fun _ h => by cases h; exact sl_19_1) (forall_cons (fun _ h => by cases h; exact sl_19_2) (forall_cons (fun _ h => by cases h; exact sl_19_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_19 : BT (Option PoolSpec) := btOfList 2 ((([(0,[]),(2,[]),(1,[]),(3,[])] : List PoolSpec)).map some)
def B_19_5 : BT (List (List Nat)) := BT.empty
lemma B_19_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 5 xs.toFinset) B_19_5 := .empty
def P_19_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_19 r_19 S_19 ps_19 [0,1,2,3]
def N_19_6 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_19_6 : checkNodesBT W_19 g_19 F_19 P_19_6 A_19 B_19_5 6 N_19_6 = true := by decide +kernel
def B_19_6 : BT (List (List Nat)) := buildBucketsBT W_19 N_19_6
set_option maxRecDepth 500000 in
lemma B_19_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_19 6 xs.toFinset) B_19_6 :=
  buildBucketsBT_sound (by decide) gp_19 W_19_ok (buildPoolsSubBT_sound S_19_ok) A_19_ok B_19_5_ok C_19_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_ok : forestRootCheck r_19 g_19 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_19_in : bucketContainsBT B_19_6 r_19 = true := by decide +kernel
lemma low_19 : Lower r_19 g_19 7 := lower_of_forestBT root_19_ok B_19_6_ok root_19_in
def g_20 := 0xfffffefefefafc00fffffefefefafc00fffffefefefafc00fffffefefefafc00
def r_20 : List Nat := varsOf 63
def p_20 : List Nat := [10,10,11,11,12,12,13,13,14,15,17,17,19,19,20,20,21,22,22,23,25,25,26,26,28,33,33,34,34,35,36,36,37,38,39,41,41,42,44,48,48,50,56,56]
def q_20 : List Nat := [8,2,9,3,8,4,9,5,6,7,16,1,18,3,16,4,5,18,6,7,24,9,24,18,24,32,1,32,2,3,32,4,5,6,7,40,9,40,40,32,16,18,40,24]
def F_20 : Nat := fullMask 44
set_option maxHeartbeats 0 in
lemma gp_20 : goodPairs g_20 p_20 q_20 := goodPairs_of (by decide +kernel)
def W_20 : BT Decor := buildWiresBT 6 (mkBase p_20 q_20 r_20) [(0,4,5),(1,4,5),(3,6,7),(0,8,0),(1,9,2),(0,0,7),(1,11,2),(1,2,6),(1,0,13),(1,1,13),(1,0,4),(1,0,5),(0,16,17),(0,18,7),(1,2,19),(3,4,5),(3,21,3),(1,21,3),(2,3,6),(1,16,5),(3,0,25),(1,3,5),(2,3,5),(0,4,17),(1,2,29),(3,0,4),(0,31,5),(1,32,2),(3,32,7),(0,16,5),(1,1,35),(1,3,6),(1,2,35),(3,18,7),(1,1,6),(2,0,6),(2,0,13),(2,4,5),(3,6,27),(3,0,5),(3,45,4),(3,31,5),(1,31,5),(3,21,27),(2,16,5),(1,45,4),(1,45,3),(3,4,17),(2,31,5),(3,16,5),(1,21,0),(1,43,0)]
lemma W_20_ok : btAll (fun x => faithful p_20 q_20 x ∧ x.1 < 2^256) W_20 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_20 : List (List (Nat × Nat)) := [[]]
def A_20 : BT (List (Nat × Nat)) := btOfList 1 al_20
set_option maxHeartbeats 0 in
lemma A_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_20 = g_20) A_20 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_20_0 : Slice r_20 g_20 (identDom 0 3) 8 := by
  have hc : Lower (varsOf 55) 0xfffffefefafaa8a8fffffefefafaa8a8fffffefefafaa8a8fffffefefafaa8a8 8 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,5),(4,5)]) (by decide +kernel) low_4
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_1 : Slice r_20 g_20 (subcubeFast 2 0) 7 := by
  have hc : Lower (varsOf 61) 0xfffffafafafaf000fffffafafafaf000fffffafafafaf000fffffafafafaf000 7 := carry_of (swaps := [(0,1),(1,5),(2,4),(3,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_2 : Slice r_20 g_20 (subcubeFast 4 0) 7 := by
  have hc : Lower (varsOf 59) 0xffffeeeeeeaacc00ffffeeeeeeaacc00ffffeeeeeeaacc00ffffeeeeeeaacc00 7 := carry_of (swaps := [(0,1),(1,3),(2,5),(4,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_3 : Slice r_20 g_20 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 55) 0xfffffefefafa0000fffffefefafa0000fffffefefafa0000fffffefefafa0000 6 := carry_of (swaps := [(0,1),(3,5),(4,5)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_4 : Slice r_20 g_20 (subcubeFast 0 8) 6 := by
  have hc : Lower (varsOf 55) 0xfffffefefefefcfcfffffefefefefcfcfffffefefefefcfcfffffefefefefcfc 6 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_5 : Slice r_20 g_20 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 62) 0xfffffcfcfcf0fc00fffffcfcfcf0fc00fffffcfcfcf0fc00fffffcfcfcf0fc00 6 := carry_of (swaps := [(0,5),(2,3),(4,5)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_6 : Slice r_20 g_20 (subcubeFast 9 0) 5 := by
  have hc : Lower (varsOf 54) 0xfffffcfcf0f00000fffffcfcf0f00000fffffcfcf0f00000fffffcfcf0f00000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 9) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_20_7 : Slice r_20 g_20 (identDom 1 4) 7 := by
  have hc : Lower (varsOf 47) 0xfefefefefcc8fcc8fefefefefcc8fcc8fefefefefcc8fcc8fefefefefcc8fcc8 7 := carry_of (swaps := [(1,4),(3,4),(4,5)]) (by decide +kernel) low_19
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
def S_20 : BT (Option (Nat × Nat)) := btOfList 3 [some (identDom 0 3,8),some (subcubeFast 2 0,7),some (subcubeFast 4 0,7),some (subcubeFast 8 0,6),some (subcubeFast 0 8,6),some (subcubeFast 1 0,6),some (subcubeFast 9 0,5),some (identDom 1 4,7)]
lemma S_20_ok : btAll (fun o => ∀ p, o = some p → Slice r_20 g_20 p.1 p.2) S_20 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (forall_cons (fun _ h => by cases h; exact sl_20_4) (forall_cons (fun _ h => by cases h; exact sl_20_5) (forall_cons (fun _ h => by cases h; exact sl_20_6) (forall_cons (fun _ h => by cases h; exact sl_20_7) (fun _ h => (List.not_mem_nil h).elim)))))))))
def ps_20 : BT (Option PoolSpec) := btOfList 7 ((([(2,[(0,4,5),(1,4,5),(3,6,7)]),(0,[(0,4,5),(1,3,6),(1,4,5)]),(1,[(0,4,5),(1,2,6),(1,4,5)]),(5,[]),(1,[(0,4,5),(1,0,6),(1,4,5)]),(2,[(0,4,5),(1,0,6),(1,4,5)]),(0,[(0,4,5),(1,0,6),(1,4,5)]),(7,[(1,3,5),(1,4,5)]),(1,[(0,4,5),(1,4,5),(3,6,7)]),(3,[]),(2,[(2,4,5),(3,4,5)]),(7,[]),(1,[]),(2,[]),(4,[]),(0,[]),(5,[(1,45,3)]),(2,[(0,4,5),(1,0,6)]),(2,[(0,4,5),(1,4,5)]),(1,[(0,4,5),(1,4,5)]),(5,[(1,3,5)]),(7,[(1,3,5)]),(1,[(1,3,5)]),(2,[(1,3,5)]),(0,[(0,4,5),(1,3,6)]),(1,[(0,4,5),(1,3,6)]),(2,[(0,4,5),(1,3,6)]),(5,[(2,3,5)]),(7,[(2,3,5)]),(1,[(2,3,5)]),(2,[(2,3,5)]),(1,[(0,4,5),(1,0,6)]),(0,[(0,4,5),(1,0,6)]),(1,[(0,4,5),(2,0,6)]),(2,[(0,4,5),(2,0,6)]),(0,[(0,4,5),(2,0,6)]),(2,[(0,4,5),(1,1,6)]),(1,[(0,4,5),(1,2,6)]),(0,[(0,4,5),(2,3,6)]),(1,[(0,4,5),(2,3,6)]),(2,[(0,4,5),(2,3,6)]),(2,[(1,4,5),(3,0,7)]),(7,[(1,4,5)]),(2,[(1,4,5)]),(1,[(1,4,5)]),(2,[(0,4,5)]),(1,[(0,4,5)]),(1,[(3,4,5)]),(2,[(3,4,5)]),(0,[(2,3,5)]),(6,[]),(1,[(2,4,5)]),(2,[(2,4,5)]),(0,[(1,3,5)]),(1,[(3,0,5)]),(2,[(3,0,5)]),(0,[(3,0,5)]),(1,[(1,0,5)]),(2,[(1,0,5)]),(0,[(1,0,5)]),(1,[(3,0,4)]),(2,[(3,0,4)]),(2,[(1,0,4)]),(1,[(1,0,4)]),(0,[(1,0,4)])] : List PoolSpec)).map some)
def B_20_2 : BT (List (List Nat)) := BT.empty
lemma B_20_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 2 xs.toFinset) B_20_2 := .empty
def P_20_3 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 []
def N_20_3 : List NodeSpec := [([8,1,10,3],[],[]),([8,1,12,3],[],[]),([3,14,15,7],[],[]),([1,3,20,7],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_3 : checkNodesBT W_20 g_20 F_20 P_20_3 A_20 B_20_2 3 N_20_3 = true := by decide +kernel
def B_20_3 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_3
set_option maxRecDepth 500000 in
lemma B_20_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 3 xs.toFinset) B_20_3 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_2_ok C_20_3
def P_20_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 []
def N_20_4 : List NodeSpec := [([8,0,1,2,22],[],[]),([8,0,1,2,23],[],[]),([9,8,1,2,3],[],[0]),([8,11,1,2,3],[],[0]),([1,12,3,6,7],[],[0]),([8,0,1,2,3],[],[]),([24,8,0,1,2],[],[]),([8,0,1,3,13],[],[]),([26,1,3,13,7],[],[]),([8,0,1,2,27],[],[]),([28,1,2,18,7],[],[]),([0,1,3,30,7],[],[]),([0,1,33,3,7],[],[]),([0,34,1,2,3],[],[]),([28,8,0,1,2],[],[]),([1,2,18,27,7],[],[]),([11,1,3,13,7],[],[0]),([28,0,1,13,7],[],[]),([1,2,3,19,7],[],[0]),([24,0,1,13,7],[],[]),([0,1,13,27,7],[],[]),([0,2,4,36,27],[],[]),([8,0,1,2,37],[],[]),([1,2,3,18,7],[],[]),([3,4,14,15,5],[],[0]),([0,1,4,38,27],[],[]),([39,1,2,3,7],[],[]),([0,3,40,13,7],[],[]),([0,1,13,37,7],[],[]),([8,0,2,3,40],[],[]),([1,3,18,13,7],[],[]),([8,26,1,2,3],[],[]),([0,1,3,38,7],[],[]),([24,1,2,18,7],[],[]),([41,8,1,2,3],[],[]),([0,2,40,37,7],[],[]),([2,3,18,40,7],[],[]),([8,1,2,3,18],[],[]),([39,8,1,2,3],[],[]),([0,1,3,13,7],[],[]),([41,1,3,13,7],[],[]),([1,3,13,14,7],[],[0]),([42,1,3,13,7],[],[]),([0,3,13,15,7],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_4 : checkNodesBT W_20 g_20 F_20 P_20_4 A_20 B_20_3 4 N_20_4 = true := by decide +kernel
def B_20_4 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_4
set_option maxRecDepth 500000 in
lemma B_20_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 4 xs.toFinset) B_20_4 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_3_ok C_20_4
def P_20_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 [0,1,2,3,4,5,6,7,8]
def N_20_5 : List NodeSpec := [([43,21,0,1,2,22],[],[0]),([43,21,0,1,2,23],[],[0]),([21,8,0,1,2,3],[],[0]),([0,1,3,4,13,5],[],[0]),([1,12,3,4,5,7],[],[0]),([8,0,1,2,3,5],[],[0]),([8,0,1,2,3,7],[],[0]),([8,0,1,2,3],[0],[0]),([26,1,2,3,6,7],[],[0]),([24,0,1,2,6,7],[],[0]),([0,1,2,6,37,7],[1],[0]),([0,1,3,6,13,7],[2],[0]),([43,8,0,1,2,3],[],[]),([24,0,1,4,13,5],[],[0]),([28,0,1,4,13,5],[],[0]),([21,1,2,3,4,18],[],[0]),([28,0,1,2,6,7],[],[0]),([11,1,2,3,6,7],[],[0]),([41,1,2,3,6,7],[],[0]),([44,0,1,2,4,5],[],[]),([0,1,4,13,5,27],[],[0]),([21,46,0,1,2,3],[],[0]),([0,1,3,4,30,5],[],[0]),([1,2,3,4,35,17],[3],[]),([1,2,3,6,18,7],[4,5,6],[0]),([31,45,1,2,3,7],[],[]),([0,1,3,13,7],[2],[0]),([43,0,47,1,2,3],[],[0]),([1,2,3,4,18,5],[],[0]),([0,1,2,3,29,7],[],[0]),([1,2,3,16,17,7],[3],[0]),([0,1,2,3,6,7],[],[0]),([45,1,2,3,4,48],[],[]),([1,2,3,4,18,7],[],[]),([32,0,1,2,3,7],[],[0]),([1,2,4,18,5,27],[],[0]),([0,1,2,4,35,27],[],[0]),([1,2,3,18,7],[5],[0]),([43,21,0,1,2,3],[],[0]),([0,2,3,4,36,5],[],[0]),([43,21,0,1,2,27],[],[0]),([0,1,2,49,4,5],[],[]),([1,2,3,29,16,5],[3],[]),([50,0,1,2,4,27],[],[]),([0,1,3,4,38,5],[],[0]),([26,1,2,3,4,5],[],[]),([28,26,1,2,4,5],[],[]),([41,1,2,4,37,5],[],[]),([0,1,3,4,13,7],[],[]),([28,1,2,4,18,5],[],[0]),([28,43,21,0,1,2],[],[0]),([0,1,33,3,4,5],[],[0]),([43,1,2,3,18,5],[],[0]),([0,1,2,3,18,7],[],[]),([43,0,2,3,40,5],[],[]),([26,1,2,4,5,27],[],[]),([2,3,4,18,40,5],[],[0]),([0,3,4,13,15,5],[],[0]),([41,2,3,4,40,5],[],[]),([0,2,4,40,37,5],[],[0]),([1,3,4,18,13,5],[],[0]),([43,0,1,3,13,5],[],[0]),([24,1,2,4,18,5],[],[0]),([0,1,2,6,27,7],[7],[0]),([1,2,3,18,5,7],[],[0]),([41,1,3,4,13,5],[],[0]),([0,1,2,3,35,7],[],[0]),([0,3,4,40,13,5],[],[0]),([24,0,2,4,40,5],[],[]),([31,1,2,3,51,5],[],[]),([0,2,3,6,40,7],[],[0]),([42,1,3,4,13,5],[],[0]),([1,3,4,13,14,5],[],[0]),([0,1,3,13,5,7],[],[0]),([8,0,1,2,3,4],[],[]),([21,0,1,3,4,13],[],[0]),([8,0,1,2,3,6],[0,8],[0]),([0,1,4,13,37,5],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_5 : checkNodesBT W_20 g_20 F_20 P_20_5 A_20 B_20_4 5 N_20_5 = true := by decide +kernel
def B_20_5 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_5
set_option maxRecDepth 500000 in
lemma B_20_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 5 xs.toFinset) B_20_5 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_4_ok C_20_5
def P_20_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 [3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42]
def N_20_6 : List NodeSpec := [([21,0,1,2,23,4,5],[9],[0]),([43,21,0,1,2,3,5],[],[0]),([43,21,0,1,2,3],[10],[0]),([0,1,2,3,4,5,7],[3],[0]),([0,1,2,3,6,4,5],[3,9,11,12,13,14],[0]),([45,0,1,2,52,4,5],[15,16],[]),([1,2,3,4,18,5],[17],[0]),([45,1,2,3,4,5,17],[3],[]),([0,1,2,3,6,7],[18,19],[0]),([21,0,1,2,3,4,17],[3],[]),([43,21,0,1,2,3,4],[],[0]),([0,1,2,6,4,5,27],[20,21,22,23],[0]),([26,1,2,3,4,5,7],[3],[0]),([31,0,1,2,3,5,7],[3],[0]),([31,45,1,2,3,4,5],[],[0]),([31,0,1,2,4,5,27],[20],[]),([0,1,2,3,4,5,25],[],[0]),([21,0,1,2,4,5,27],[],[0]),([43,31,0,1,2,3,5],[3],[0]),([45,0,1,2,3,4,7],[3],[0]),([21,0,1,2,22,4,5],[14],[0]),([0,1,2,3,29,4,5],[3,9,11,12,13,14],[0]),([1,2,3,4,16,5,17],[],[0]),([0,1,2,4,16,5,27],[20],[0]),([21,45,0,1,2,3,4],[3],[0]),([0,1,2,6,4,37,5],[9,24,25,26],[0]),([53,0,1,2,3,4,5],[],[]),([32,0,1,2,3,4,5],[11,12,13,14,15],[0]),([0,1,2,3,4,17,7],[3],[0]),([0,1,2,3,16,5,7],[3],[0]),([54,0,1,2,3,4,5],[],[]),([28,43,0,1,2,4,5],[],[0]),([43,0,1,2,3,16,5],[3],[]),([31,1,2,3,4,16,5],[3],[]),([46,0,1,2,3,4,5],[3],[0]),([43,0,1,2,4,5,27],[],[0]),([0,1,2,3,4,5,48],[],[0]),([0,1,2,3,4,51,5],[],[0]),([50,0,1,2,3,4,5],[],[0]),([0,47,1,2,3,4,5],[3,9,14],[0]),([55,0,1,2,3,4,5],[14,15],[]),([28,0,1,2,6,4,5],[27,28,29,30],[0]),([0,56,1,2,3,4,5],[],[]),([21,0,1,2,3,4,5],[9,14],[0]),([28,0,1,2,4,5,7],[27],[0]),([28,21,0,1,2,4,5],[],[0]),([0,1,2,3,4,18,5],[],[0]),([1,2,3,6,4,18,5],[3,17,31,32],[0]),([41,1,2,3,6,4,5],[33,34,35],[0]),([0,2,3,6,4,40,5],[12,36],[0]),([0,1,3,4,13,5],[37],[0]),([0,1,2,3,4,35,5],[3,9,12,13,14],[0]),([0,1,3,6,4,13,5],[13,37],[0]),([24,0,1,2,6,4,5],[14,38,39,40],[0]),([0,1,2,4,5,27,7],[20],[0]),([43,0,1,2,3,6,5],[15],[0]),([21,0,1,2,3,5,7],[15],[0]),([21,0,1,2,3,6,4],[15],[0]),([45,0,1,2,4,5,27],[15,20],[]),([43,0,1,2,3,4,7],[15],[0]),([0,1,2,3,6,4,7],[],[0]),([26,1,2,3,4,5],[41],[0]),([0,1,2,3,6,5,7],[42],[0]),([26,0,1,2,3,4,5],[],[]),([11,1,2,3,4,5,7],[],[0]),([43,0,1,2,3,4,5],[],[0]),([0,57,1,2,3,4,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_6 : checkNodesBT W_20 g_20 F_20 P_20_6 A_20 B_20_5 6 N_20_6 = true := by decide +kernel
def B_20_6 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_6
set_option maxRecDepth 500000 in
lemma B_20_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 6 xs.toFinset) B_20_6 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_5_ok C_20_6
def P_20_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 [3,9,11,12,13,14,15,20,22,23,27,29,30,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64]
def N_20_7 : List NodeSpec := [([0,1,2,3,4,5,7],[3,9,14,43,44],[0]),([0,1,2,3,6,4,5],[3,9,11,12,14,45,46],[0]),([21,0,1,2,3,4,5],[3,9,12,13,14,47,48],[0]),([28,0,1,2,4,5],[9,14,27,29,30,49,50],[0]),([43,0,1,2,3,4,5],[3,9,12,13,14,51,52],[0]),([0,1,2,4,5,27],[9,14,20,22,23,53],[0]),([45,0,1,2,3,4,5],[3,12,13,14,15,50,54,55,56],[0]),([0,1,2,3,4,5,17],[3,50,57,58,59],[0]),([31,0,1,2,3,4,5],[3,12,13,14,15,50,60,61],[0]),([0,1,2,3,4,16,5],[3,12,14,15,50,62,63,64],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_7 : checkNodesBT W_20 g_20 F_20 P_20_7 A_20 B_20_6 7 N_20_7 = true := by decide +kernel
def B_20_7 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_7
set_option maxRecDepth 500000 in
lemma B_20_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 7 xs.toFinset) B_20_7 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_6_ok C_20_7
def P_20_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_20 r_20 S_20 ps_20 [3,9,12,13,14,15]
def N_20_8 : List NodeSpec := [([0,1,2,3,4,5],[3,9,12,13,14,15],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_20_8 : checkNodesBT W_20 g_20 F_20 P_20_8 A_20 B_20_7 8 N_20_8 = true := by decide +kernel
def B_20_8 : BT (List (List Nat)) := buildBucketsBT W_20 N_20_8
set_option maxRecDepth 500000 in
lemma B_20_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_20 8 xs.toFinset) B_20_8 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok (buildPoolsSubBT_sound S_20_ok) A_20_ok B_20_7_ok C_20_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck r_20 g_20 [(VAR 0,16,17),(VAR 1,8,10),(VAR 2,8,12),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,1,33)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT B_20_8 r_20 = true := by decide +kernel
lemma low_20 : Lower r_20 g_20 9 := lower_of_forestBT root_20_ok B_20_8_ok root_20_in
def g_21 := 0xfffefcc0fffefcc0fffefcc0fffefcc0fffefcc0fffefcc0fffefcc0fffefcc0
def r_21 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_21 : Lower r_21 g_21 8 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_22 := 0xfeeefac0feeefac0feeefac0feeefac0feeefac0feeefac0feeefac0feeefac0
def r_22 : List Nat := varsOf 31
def p_22 : List Nat := [6,6,7,7,9,9,11,11,12,12,13,14,17,17,18,18,19,21,21,22,25,26,26,28,28]
def q_22 : List Nat := [4,2,5,3,8,1,10,3,8,4,5,10,16,1,16,2,3,20,5,20,24,24,10,24,20]
def F_22 : Nat := fullMask 25
set_option maxHeartbeats 0 in
lemma gp_22 : goodPairs g_22 p_22 q_22 := goodPairs_of (by decide +kernel)
def W_22 : BT Decor := buildWiresBT 3 (mkBase p_22 q_22 r_22) [(1,0,1),(2,5,4),(1,1,2)]
lemma W_22_ok : btAll (fun x => faithful p_22 q_22 x ∧ x.1 < 2^256) W_22 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_22 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)],[(0,1),(2,3)],[(0,2),(1,2),(2,4),(3,4)],[(0,1),(1,3),(2,3),(3,4)],[(0,2),(1,4)],[(0,3),(2,4)],[(0,4),(1,2),(2,3),(3,4)],[(0,3),(1,4),(2,4),(3,4)]]
def A_22 : BT (List (Nat × Nat)) := btOfList 4 al_22
set_option maxHeartbeats 0 in
lemma A_22_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_22 = g_22) A_22 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_22_0 : Slice r_22 g_22 (identDom 0 1) 5 := by
  have hc : Lower (varsOf 29) 0xfaaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0 5 := carry_of (swaps := [(0,3),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_1 : Slice r_22 g_22 (identDom 0 2) 5 := by
  have hc : Lower (varsOf 27) 0xeeeeaa88eeeeaa88eeeeaa88eeeeaa88eeeeaa88eeeeaa88eeeeaa88eeeeaa88 5 := carry_of (swaps := [(0,3),(2,4)]) (by decide +kernel) low_1
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_2 : Slice r_22 g_22 (subcubeFast 1 0) 4 := by
  have hc : Lower (varsOf 30) 0xfcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0fcccf0c0 4 := carry_of (swaps := [(0,4),(1,2),(2,3),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_3 : Slice r_22 g_22 (subcubeFast 2 0) 4 := by
  have hc : Lower (varsOf 29) 0xfaaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00faaafa00 4 := carry_of (swaps := [(0,2),(1,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_4 : Slice r_22 g_22 (subcubeFast 4 0) 4 := by
  have hc : Lower (varsOf 27) 0xeeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00eeeeaa00 4 := carry_of (swaps := [(0,2),(1,2),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_5 : Slice r_22 g_22 (subcubeFast 8 0) 4 := by
  have hc : Lower (varsOf 23) 0xeeeec0c0eeeec0c0eeeec0c0eeeec0c0eeeec0c0eeeec0c0eeeec0c0eeeec0c0 4 := carry_of (swaps := [(1,2),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_22_6 : Slice r_22 g_22 (subcubeFast 16 0) 4 := by
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) low_7
def S_22 : BT (Option (Nat × Nat)) := btOfList 3 [some (identDom 0 1,5),some (identDom 0 2,5),some (subcubeFast 1 0,4),some (subcubeFast 2 0,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,4),some (subcubeFast 16 0,4)]
lemma S_22_ok : btAll (fun o => ∀ p, o = some p → Slice r_22 g_22 p.1 p.2) S_22 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_22_0) (forall_cons (fun _ h => by cases h; exact sl_22_1) (forall_cons (fun _ h => by cases h; exact sl_22_2) (forall_cons (fun _ h => by cases h; exact sl_22_3) (forall_cons (fun _ h => by cases h; exact sl_22_4) (forall_cons (fun _ h => by cases h; exact sl_22_5) (forall_cons (fun _ h => by cases h; exact sl_22_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_22 : BT (Option PoolSpec) := btOfList 3 ((([(3,[]),(0,[]),(6,[]),(2,[]),(1,[]),(5,[]),(4,[])] : List PoolSpec)).map some)
def B_22_3 : BT (List (List Nat)) := BT.empty
lemma B_22_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 3 xs.toFinset) B_22_3 := .empty
def P_22_4 : BT (Option BoundPool) := buildPoolsSubBT 3 W_22 r_22 S_22 ps_22 []
def N_22_4 : List NodeSpec := [([6,0,1,2,3],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_4 : checkNodesBT W_22 g_22 F_22 P_22_4 A_22 B_22_3 4 N_22_4 = true := by decide +kernel
def B_22_4 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_4
set_option maxRecDepth 500000 in
lemma B_22_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 4 xs.toFinset) B_22_4 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_3_ok C_22_4
def P_22_5 : BT (Option BoundPool) := buildPoolsSubBT 3 W_22 r_22 S_22 ps_22 [0,1,2]
def N_22_5 : List NodeSpec := [([0,1,2,7,3,4],[0],[]),([0,1,5,2,3,4],[1,2],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_5 : checkNodesBT W_22 g_22 F_22 P_22_5 A_22 B_22_4 5 N_22_5 = true := by decide +kernel
def B_22_5 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_5
set_option maxRecDepth 500000 in
lemma B_22_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 5 xs.toFinset) B_22_5 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_4_ok C_22_5
def P_22_6 : BT (Option BoundPool) := buildPoolsSubBT 3 W_22 r_22 S_22 ps_22 [0,1,2,3,4,5,6]
def N_22_6 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3,4,5,6],[0,1,2,3,4,5,6,7,8])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_22_6 : checkNodesBT W_22 g_22 F_22 P_22_6 A_22 B_22_5 6 N_22_6 = true := by decide +kernel
def B_22_6 : BT (List (List Nat)) := buildBucketsBT W_22 N_22_6
set_option maxRecDepth 500000 in
lemma B_22_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_22 6 xs.toFinset) B_22_6 :=
  buildBucketsBT_sound (by decide) gp_22 W_22_ok (buildPoolsSubBT_sound S_22_ok) A_22_ok B_22_5_ok C_22_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_ok : forestRootCheck r_22 g_22 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_22_in : bucketContainsBT B_22_6 r_22 = true := by decide +kernel
lemma low_22 : Lower r_22 g_22 7 := lower_of_forestBT root_22_ok B_22_6_ok root_22_in
def g_23 := 0xfffffffcfeeefac0fffffffcfeeefac0fffffffcfeeefac0fffffffcfeeefac0
def r_23 : List Nat := varsOf 63
def p_23 : List Nat := [6,6,7,7,9,9,11,11,12,12,13,14,17,17,18,18,19,21,21,22,25,26,26,28,28,34,34,35,35,36,36,37,37,40,40,41,42,48,48,49,52,56]
def q_23 : List Nat := [4,2,5,3,8,1,10,3,8,4,5,10,16,1,16,2,3,20,5,20,24,24,10,24,20,32,2,33,3,32,4,33,5,32,8,33,10,32,16,33,20,24]
def F_23 : Nat := fullMask 42
set_option maxHeartbeats 0 in
lemma gp_23 : goodPairs g_23 p_23 q_23 := goodPairs_of (by decide +kernel)
def W_23 : BT Decor := buildWiresBT 8 (mkBase p_23 q_23 r_23) [(1,1,2),(0,1,2),(1,7,5),(0,6,8),(1,9,4),(1,0,8),(1,2,4),(1,3,5),(0,12,13),(1,3,4),(1,2,5),(2,6,8),(1,0,5),(3,7,6),(2,6,5),(1,1,5),(0,12,21),(1,3,22),(1,4,5),(0,6,24),(0,2,24),(1,2,24),(3,26,27),(1,0,9),(1,1,4),(1,1,3),(0,31,12),(0,6,13),(1,1,24),(3,4,34),(1,35,3),(3,2,36),(3,4,27),(3,38,0),(1,39,5),(0,2,21),(1,41,4),(1,6,8),(2,1,4),(1,44,3),(1,45,5),(3,2,46),(2,2,3),(1,48,1),(3,2,24),(1,3,30),(1,51,5),(3,2,52),(0,31,24),(0,31,16),(1,55,4),(1,2,3),(2,31,5),(1,1,13),(3,3,59),(1,3,12),(2,2,4),(1,62,1),(2,1,2),(3,2,13),(1,65,1),(0,1,13),(1,19,5),(2,2,24),(2,6,4),(3,2,59),(3,41,43),(2,70,5),(2,49,5),(3,48,24),(3,2,31),(1,6,3),(3,2,21),(3,1,16),(3,1,24),(1,69,4),(1,64,3),(2,2,1),(1,83,4),(2,77,5),(2,63,5),(1,6,4),(1,20,3),(1,41,3),(1,44,48),(3,7,43),(3,1,13),(3,1,12),(1,62,5),(1,77,4),(2,95,5),(3,3,24),(1,97,1),(3,4,13),(1,99,1),(1,15,5),(3,0,15),(1,102,5),(2,1,5),(1,104,3),(3,2,105),(1,38,0),(1,38,3),(3,15,21),(1,50,3),(2,51,5),(2,82,5),(2,1,3),(3,113,16),(3,4,43),(1,70,3),(1,2,13),(3,4,117),(3,2,101),(2,2,5),(3,120,6),(1,48,4),(1,80,3),(1,113,2),(0,1,16),(3,4,59),(3,12,21),(2,77,4),(2,6,3),(3,120,12),(1,64,5),(1,77,5),(1,83,5),(1,38,1),(1,120,44),(1,120,1),(1,44,5),(3,3,12),(1,138,1),(0,6,18),(3,62,16),(1,44,2),(3,2,45),(2,1,16),(3,6,18),(3,4,31),(1,7,4),(1,50,1),(3,83,18),(3,83,16),(3,7,18),(3,2,18),(1,152,1),(0,2,18),(1,154,1),(3,3,117),(1,156,1),(3,113,18),(3,6,13),(1,93,3),(1,0,21),(3,4,161),(2,12,5),(1,163,1),(1,44,57),(2,70,3),(1,125,4),(3,83,24),(3,1,18),(1,104,57),(3,48,21),(3,48,16),(2,49,4),(1,0,2),(2,76,4),(1,163,3),(1,76,5),(2,136,4),(3,2,51),(1,146,5),(2,146,5),(3,30,16),(3,2,137),(0,1,27),(1,82,5),(2,45,5),(3,12,13),(3,4,133),(1,63,5),(1,48,5),(3,4,190),(2,76,5),(1,0,94),(1,70,5),(1,113,5),(3,2,195),(3,2,34),(3,30,13),(1,49,5),(1,0,16),(1,104,2),(1,78,3),(1,79,3),(3,0,21),(2,0,5),(3,0,6),(1,0,6),(1,0,3),(0,1,18),(1,0,1)]
lemma W_23_ok : btAll (fun x => faithful p_23 q_23 x ∧ x.1 < 2^256) W_23 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_23 : List (List (Nat × Nat)) := [[],[(1,2),(3,4)]]
def A_23 : BT (List (Nat × Nat)) := btOfList 1 al_23
set_option maxHeartbeats 0 in
lemma A_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_23 = g_23) A_23 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_23_0 : Slice r_23 g_23 (identDom 0 1) 8 := by
  have hc : Lower (varsOf 61) 0xfffffffafaaafaa0fffffffafaaafaa0fffffffafaaafaa0fffffffafaaafaa0 8 := carry_of (swaps := [(0,3),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_4
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_1 : Slice r_23 g_23 (identDom 0 2) 8 := by
  have hc : Lower (varsOf 59) 0xffffffeeeeeeaa88ffffffeeeeeeaa88ffffffeeeeeeaa88ffffffeeeeeeaa88 8 := carry_of (swaps := [(0,3),(2,5),(4,5)]) (by decide +kernel) low_4
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_2 : Slice r_23 g_23 (identDom 3 4) 8 := by
  have hc : Lower (varsOf 47) 0xfffcfffcfec0fec0fffcfffcfec0fec0fffcfffcfec0fec0fffcfffcfec0fec0 8 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_21
  exact slice_ident (u := 3) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_3 : Slice r_23 g_23 (subcubeFast 1 0) 7 := by
  have hc : Lower (varsOf 62) 0xfffffffcfcccf0c0fffffffcfcccf0c0fffffffcfcccf0c0fffffffcfcccf0c0 7 := carry_of (swaps := [(0,5),(1,2),(2,3),(3,5),(4,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_4 : Slice r_23 g_23 (subcubeFast 8 0) 7 := by
  have hc : Lower (varsOf 55) 0xfffffcfceeeec0c0fffffcfceeeec0c0fffffcfceeeec0c0fffffcfceeeec0c0 7 := carry_of (swaps := [(1,2),(3,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_5 : Slice r_23 g_23 (subcubeFast 16 0) 7 := by
  have hc : Lower (varsOf 47) 0xfffcfffcfac0fac0fffcfffcfac0fac0fffcfffcfac0fac0fffcfffcfac0fac0 7 := carry_of (swaps := [(3,4),(4,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_6 : Slice r_23 g_23 (subcubeFast 32 0) 7 := by
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) low_22
set_option maxHeartbeats 0 in
lemma sl_23_7 : Slice r_23 g_23 (subcubeFast 19 0) 4 := by
  have hc : Lower (varsOf 44) 0xfff0fff0f000f000fff0fff0f000f000fff0fff0f000f000fff0fff0f000f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 19) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_8 : Slice r_23 g_23 (subcubeFast 13 0) 4 := by
  have hc : Lower (varsOf 50) 0xffffcccccccc0000ffffcccccccc0000ffffcccccccc0000ffffcccccccc0000 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 13) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_9 : Slice r_23 g_23 (subcubeFast 25 0) 4 := by
  have hc : Lower (varsOf 38) 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 25) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_23_10 : Slice r_23 g_23 (subcubeFast 24 1) 4 := by
  have hc : Lower (varsOf 38) 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 24) (o := 1) (by decide +kernel) hc
def S_23 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,8),some (identDom 0 2,8),some (identDom 3 4,8),some (subcubeFast 1 0,7),some (subcubeFast 8 0,7),some (subcubeFast 16 0,7),some (subcubeFast 32 0,7),some (subcubeFast 19 0,4),some (subcubeFast 13 0,4),some (subcubeFast 25 0,4),some (subcubeFast 24 1,4)]
lemma S_23_ok : btAll (fun o => ∀ p, o = some p → Slice r_23 g_23 p.1 p.2) S_23 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (forall_cons (fun _ h => by cases h; exact sl_23_4) (forall_cons (fun _ h => by cases h; exact sl_23_5) (forall_cons (fun _ h => by cases h; exact sl_23_6) (forall_cons (fun _ h => by cases h; exact sl_23_7) (forall_cons (fun _ h => by cases h; exact sl_23_8) (forall_cons (fun _ h => by cases h; exact sl_23_9) (forall_cons (fun _ h => by cases h; exact sl_23_10) (fun _ h => (List.not_mem_nil h).elim))))))))))))
def ps_23 : BT (Option PoolSpec) := btOfList 8 ((([(5,[(0,2,24),(1,2,24),(3,26,27)]),(6,[]),(8,[]),(4,[(1,2,4)]),(3,[(0,1,2),(1,7,5),(1,1,2)]),(4,[(0,1,2),(1,7,5),(1,1,2)]),(5,[(0,1,2),(1,7,5),(1,1,2)]),(6,[(0,1,2),(1,1,2)]),(6,[(0,1,2),(1,1,2),(3,7,6)]),(3,[(1,2,1),(1,2,4),(1,1,3)]),(5,[(1,1,3)]),(9,[]),(7,[]),(6,[(0,2,21),(1,2,21),(3,41,43)]),(6,[(0,1,2),(1,1,2),(2,6,8)]),(6,[(0,1,2),(1,1,2),(3,7,43)]),(4,[]),(5,[]),(10,[]),(2,[(1,4,5),(3,4,101)]),(5,[(2,2,24),(3,2,24)]),(4,[(1,1,13),(3,2,59)]),(0,[]),(2,[(1,15,5),(3,4,101)]),(6,[(1,3,4),(3,0,15)]),(6,[(3,4,16),(1,38,0)]),(2,[]),(3,[]),(6,[(1,3,21),(3,2,59)]),(3,[(1,1,5),(3,4,21)]),(4,[(1,1,5),(3,2,21)]),(6,[(2,1,2),(3,1,16)]),(4,[(0,1,2),(1,1,2),(3,7,6)]),(4,[(1,31,5),(3,2,59)]),(4,[(1,0,5)]),(3,[(1,1,3),(1,2,4)]),(3,[(1,2,4),(1,2,5)]),(6,[(1,1,3),(3,2,59)]),(3,[(0,1,2),(1,1,2),(3,7,6)]),(6,[(1,1,3),(3,2,31)]),(6,[(2,1,16),(3,1,16)]),(0,[(1,0,5)]),(2,[(1,1,3),(3,4,51)]),(4,[(1,0,5),(1,2,4),(1,4,5)]),(5,[(1,0,5)]),(3,[(0,1,2),(3,7,18)]),(2,[(1,3,5)]),(3,[(1,4,5)]),(6,[(2,1,3),(3,113,18)]),(3,[(1,2,4)]),(6,[(1,0,21),(3,4,161)]),(4,[(0,1,13),(1,1,13)]),(6,[(0,1,16),(1,125,4)]),(3,[(1,2,1),(1,2,4)]),(0,[(1,2,4)]),(1,[]),(6,[(1,2,1)]),(6,[(0,1,2),(3,7,18)]),(6,[(0,2,21),(1,41,4)]),(6,[(0,1,16),(1,1,16)]),(6,[(1,4,16),(0,1,27)]),(1,[(1,2,5),(3,2,200)]),(5,[(3,2,24)]),(6,[(3,2,24)]),(1,[(1,4,5)]),(5,[(2,2,24)]),(4,[(0,1,13)]),(6,[(1,3,4)]),(0,[(1,3,4),(3,0,15)]),(6,[(3,4,21)]),(3,[(1,2,5)]),(5,[(1,2,5)]),(6,[(3,4,16)]),(3,[(1,1,5)]),(6,[(3,2,21)]),(6,[(1,3,21)]),(4,[(1,1,5)]),(6,[(2,1,16)]),(6,[(1,2,21)]),(0,[(1,1,5),(3,0,21)]),(6,[(3,0,21)]),(0,[(1,1,5)]),(6,[(1,0,21)]),(5,[(1,1,5)]),(6,[(2,1,4)]),(5,[(2,2,3)]),(4,[(2,1,4)]),(6,[(1,2,3)]),(6,[(1,1,4)]),(2,[(1,2,3)]),(5,[(1,2,3)]),(1,[(1,1,5)]),(4,[(2,31,5)]),(6,[(1,1,3)]),(6,[(3,4,13)]),(4,[(1,31,5)]),(2,[(1,1,3)]),(4,[(2,31,4)]),(3,[(1,1,3)]),(1,[(1,1,5),(3,2,21)]),(0,[(1,1,3)]),(4,[(2,1,5)]),(6,[(2,1,2)]),(0,[(1,1,2),(3,0,6)]),(4,[(1,2,4),(1,1,4)]),(0,[(1,1,2)]),(3,[(0,2,1),(1,7,4)]),(4,[(0,2,1),(1,7,4)]),(3,[(0,1,2),(1,7,5)]),(6,[(2,2,4)]),(5,[(1,62,5)]),(6,[(0,1,2)]),(6,[(1,0,3)]),(5,[(1,0,5),(1,1,3)]),(3,[(1,3,5)]),(6,[(1,1,2)]),(6,[(2,2,3)]),(0,[(2,0,5)]),(3,[(1,1,2)]),(4,[(1,1,4)]),(6,[(1,4,3)]),(0,[(1,2,5)]),(1,[(1,0,1)]),(6,[(1,0,1)]),(6,[(0,1,16)]),(5,[(1,0,5),(1,3,5)]),(6,[(1,4,21)]),(0,[(1,3,4)]),(5,[(1,2,1)]),(6,[(3,2,18)]),(3,[(3,2,18)]),(1,[(1,0,5)]),(3,[(0,1,2),(1,1,2)]),(4,[(0,1,2),(1,1,2)]),(3,[(2,1,2),(1,64,3)]),(6,[(1,2,4)]),(6,[(3,2,13)]),(4,[(1,2,31)]),(4,[(3,2,31)]),(4,[(1,1,13)]),(3,[(2,1,5),(1,104,3)]),(6,[(1,104,3)]),(6,[(1,120,1)]),(4,[(1,2,5)]),(3,[(1,3,4)]),(1,[(2,1,2)]),(3,[(1,2,3)]),(3,[(0,1,2)]),(3,[(2,1,5)]),(3,[(2,2,4)]),(3,[(2,1,4)])] : List PoolSpec)).map some)
def B_23_2 : BT (List (List Nat)) := BT.empty
lemma B_23_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 2 xs.toFinset) B_23_2 := .empty
def P_23_3 : BT (Option BoundPool) := buildPoolsSubBT 8 W_23 r_23 S_23 ps_23 []
def N_23_3 : List NodeSpec := [([6,3,10,11],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_3 : checkNodesBT W_23 g_23 F_23 P_23_3 A_23 B_23_2 3 N_23_3 = true := by decide +kernel
def B_23_3 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_3
set_option maxRecDepth 500000 in
lemma B_23_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 3 xs.toFinset) B_23_3 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_2_ok C_23_3
def P_23_4 : BT (Option BoundPool) := buildPoolsSubBT 8 W_23 r_23 S_23 ps_23 []
def N_23_4 : List NodeSpec := [([0,1,14,15,16],[],[]),([17,6,3,4,18],[],[]),([17,19,3,4,18],[],[]),([0,6,3,10,8],[],[0]),([20,19,3,4,18],[],[]),([0,1,4,23,16],[],[]),([1,25,3,12,18],[],[]),([28,1,3,4,18],[],[]),([17,6,3,4,11],[],[]),([9,6,3,4,11],[],[0,1]),([6,29,3,4,8],[],[]),([0,6,3,22,24],[],[]),([0,3,30,22,16],[],[]),([0,6,32,15,5],[],[]),([0,33,31,4,16],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_4 : checkNodesBT W_23 g_23 F_23 P_23_4 A_23 B_23_3 4 N_23_4 = true := by decide +kernel
def B_23_4 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_4
set_option maxRecDepth 500000 in
lemma B_23_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 4 xs.toFinset) B_23_4 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_3_ok C_23_4
def P_23_5 : BT (Option BoundPool) := buildPoolsSubBT 8 W_23 r_23 S_23 ps_23 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def N_23_5 : List NodeSpec := [([28,0,1,3,4,5],[0],[0]),([37,0,1,3,4,5],[],[]),([38,1,2,3,4,40],[],[]),([0,1,3,42,5,43],[],[]),([47,0,1,3,4,5],[],[]),([0,49,3,4,21,16],[1],[]),([38,50,0,1,3,5],[],[]),([53,0,1,3,4,5],[],[]),([0,1,2,54,15,5],[],[1]),([0,1,2,3,56,5],[],[1]),([0,1,2,3,22,24],[1],[0]),([50,0,2,3,30,21],[],[]),([0,1,55,57,4,5],[2],[1]),([58,60,0,1,2,4],[],[]),([0,1,3,4,14,16],[1],[0]),([0,1,4,61,16,13],[1,3],[]),([0,63,3,4,21,16],[],[]),([0,1,3,4,22,16],[1],[0]),([64,0,66,3,4,5],[],[]),([64,65,0,31,4,5],[],[]),([0,9,6,3,4,8],[4,5,6,7],[0,1]),([20,19,0,3,4,5],[],[0]),([67,2,31,4,18,13],[],[]),([0,6,3,4,5,68],[8],[]),([35,1,2,3,18,24],[],[]),([0,6,31,12,15,5],[3,9,10,11],[0]),([69,50,1,3,4,18],[],[0]),([38,1,2,3,18,24],[12],[]),([70,0,3,4,21,16],[],[]),([71,1,3,4,18,13],[],[]),([72,0,1,3,4,5],[13],[]),([0,1,57,4,16,59],[2],[]),([17,0,6,3,4,8],[14],[0]),([73,1,2,3,4,18],[],[]),([19,0,3,4,5,43],[],[]),([74,1,2,3,4,18],[],[]),([0,1,2,32,15,5],[],[0]),([0,3,30,12,21,16],[12],[0]),([65,1,57,4,18,13],[],[]),([0,1,2,75,15,5],[],[]),([6,3,4,18,8],[7,12],[0]),([20,1,2,3,4,18],[],[]),([76,1,2,4,18,13],[],[]),([0,1,77,4,16,13],[1],[]),([78,79,0,3,4,5],[],[]),([19,3,4,5,18],[2,8,12],[0]),([35,80,0,2,3,5],[],[]),([19,6,3,4,5,18],[8],[0]),([0,6,3,32,4,5],[],[0]),([1,2,3,81,18,24],[],[]),([20,1,3,4,12,18],[],[]),([64,2,31,4,18,13],[],[]),([0,6,3,42,5,21],[],[]),([0,1,12,15,16,13],[11],[0]),([67,2,3,4,18,59],[],[1]),([38,0,6,3,4,21],[],[]),([1,6,3,12,18,24],[],[0]),([65,0,1,82,4,5],[],[]),([1,2,3,84,18,24],[],[]),([85,1,2,3,4,18],[],[]),([20,62,1,3,4,18],[],[]),([86,1,2,3,4,18],[],[]),([1,2,33,3,4,18],[1],[1]),([1,2,3,87,18,24],[1],[]),([6,3,4,5,8,11],[12],[]),([1,2,3,88,4,18],[],[]),([20,0,6,3,4,8],[],[]),([0,1,89,4,21,16],[],[]),([17,0,6,3,4,5],[14],[0]),([0,1,3,42,21,16],[],[]),([19,0,3,4,5,68],[8],[]),([90,0,1,2,15,5],[],[]),([91,0,6,3,4,5],[15],[]),([20,7,6,3,4,18],[],[0]),([0,6,3,12,21,24],[],[0,1]),([58,92,0,2,3,4],[],[]),([0,6,3,4,21,27],[12],[]),([70,93,0,2,3,5],[],[]),([0,6,3,55,4,5],[2],[1]),([71,0,1,3,4,5],[],[]),([0,1,25,3,12,5],[],[0,1]),([6,3,4,8,11],[2,12],[0]),([50,1,3,12,18,24],[],[]),([0,6,3,4,94,21],[],[]),([0,3,77,4,21,16],[1],[]),([0,1,33,3,4,16],[1,2],[0]),([20,78,0,1,3,4],[],[]),([17,19,0,3,4,5],[8],[0]),([96,0,1,2,3,4],[],[]),([76,93,0,3,4,5],[],[]),([0,6,3,4,8,43],[7],[]),([0,6,3,4,21,16],[1,12],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_5 : checkNodesBT W_23 g_23 F_23 P_23_5 A_23 B_23_4 5 N_23_5 = true := by decide +kernel
def B_23_5 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_5
set_option maxRecDepth 500000 in
lemma B_23_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 5 xs.toFinset) B_23_5 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_4_ok C_23_5
def P_23_6 : BT (Option BoundPool) := buildPoolsSubBT 8 W_23 r_23 S_23 ps_23 [1,2,3,4,5,7,8,10,11,12,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61]
def N_23_6_0 : List NodeSpec := [([0,1,98,2,3,4,5],[16],[]),([0,1,100,2,3,4,5],[],[]),([99,0,1,2,3,5,24],[17,18,19],[]),([0,1,66,2,3,4,5],[],[0]),([69,50,0,1,3,4,5],[20],[0]),([0,1,2,3,4,94,24],[2,18],[]),([38,0,1,2,3,5,24],[17],[0]),([71,0,1,3,4,5,13],[21],[0]),([99,0,1,2,3,5,101],[18,22,23],[]),([50,0,1,2,3,15,5],[16],[]),([1,2,3,4,5,103],[11,24],[]),([106,0,1,2,3,4,5],[],[]),([0,1,2,3,36,4,5],[2],[0]),([65,0,1,3,4,5,16],[1],[1]),([50,0,1,2,3,4,21],[12],[0]),([65,0,1,3,4,16,13],[1,2],[]),([107,1,2,3,4,5,16],[25],[]),([0,1,2,3,108,4,5],[26],[]),([38,107,1,2,3,4,5],[27],[]),([71,0,1,3,4,5,21],[28],[]),([109,0,1,2,3,4,5],[18,27],[]),([35,0,1,2,3,15,5],[26,29],[]),([0,1,2,3,110,4,5],[],[]),([78,0,2,3,31,4,5],[16,30],[]),([38,83,0,1,3,4,5],[],[]),([111,0,1,2,3,4,5],[18,27],[]),([64,79,0,2,3,4,5],[31],[]),([90,0,1,2,3,4,5],[],[0]),([58,64,0,2,3,4,5],[],[]),([112,0,1,2,3,4,5],[],[]),([62,79,0,1,3,4,5],[],[]),([0,1,2,3,84,5,24],[1],[0,1]),([38,0,1,2,3,5,27],[22],[0,1]),([0,1,3,4,12,21,16],[],[0,1]),([0,1,2,33,3,4,5],[1,2],[0,1]),([0,1,2,3,114,4,5],[16],[]),([0,1,2,3,88,4,5],[],[0]),([64,0,2,3,4,5,59],[2],[]),([115,0,1,2,3,4,5],[],[]),([78,0,1,2,3,4,5],[],[]),([0,1,2,3,116,4,5],[26],[]),([85,0,1,2,3,4,5],[],[0]),([118,0,1,2,3,4,5],[],[]),([0,1,2,3,4,95,5],[1,18,22],[0]),([0,6,3,31,4,5,16],[],[0,1]),([50,0,1,3,12,5,24],[2],[0]),([38,0,1,2,3,4,21],[12],[0]),([0,1,2,3,87,5,24],[1],[0,1]),([119,0,1,2,3,4,5],[],[]),([0,1,121,6,3,4,5],[2,12],[]),([38,0,1,6,3,4,5],[],[0]),([99,0,1,2,15,5,13],[18,26],[]),([0,1,6,3,4,16,13],[],[0,1]),([0,1,3,4,61,5,16],[1,3],[0]),([0,1,2,3,122,5,24],[1,18],[]),([0,1,2,31,15,5,24],[12,18],[0,1]),([64,0,2,3,4,21,16],[1,2],[0]),([70,0,1,3,4,5,16],[],[0]),([0,1,2,3,123,4,5],[18,27],[]),([0,1,6,3,4,5,16],[1,12],[0]),([58,0,1,2,4,15,5],[17],[]),([70,0,1,2,3,15,5],[26],[]),([19,0,6,3,4,5],[2,8,12,32],[0]),([71,0,1,3,31,4,5],[33],[]),([0,1,124,3,4,5,16],[1],[1]),([50,0,1,3,4,5,16],[1],[0]),([20,0,1,2,3,4,43],[22],[0,1]),([70,0,2,3,4,5,21],[1],[0]),([0,125,6,3,4,5,16],[2],[1]),([126,0,1,2,3,4,5],[],[]),([0,1,6,3,4,21,16],[1,12],[]),([127,0,1,2,3,4,5],[],[]),([50,0,1,3,4,12,5],[17],[1]),([128,0,1,2,3,4,5],[],[]),([78,0,1,3,4,5,43],[22],[0]),([0,1,2,3,61,5,24],[1,18],[]),([62,0,6,3,4,5,21],[],[0]),([64,0,2,31,4,5,13],[12],[0]),([0,1,3,4,84,5,16],[1],[]),([104,129,0,2,3,4,5],[],[]),([70,0,1,2,3,12,5],[17],[0]),([1,2,3,30,12,5,18],[12],[]),([0,1,3,4,130,12,5],[2,3,17],[]),([0,1,3,4,122,5,16],[1],[]),([0,1,2,3,4,131,16],[1,12],[]),([0,1,2,3,4,5,132],[],[0]),([0,1,6,3,4,5,94],[],[0]),([1,63,2,3,4,5,18],[1],[0]),([0,1,3,4,12,5,133],[17],[]),([0,1,134,2,3,4,5],[],[]),([64,65,0,1,3,4,5],[],[0]),([7,6,3,4,5,18],[2,7,12],[0]),([70,0,1,6,3,12,5],[17],[]),([0,1,6,3,12,5,24],[],[0]),([62,1,6,3,4,5,18],[],[0]),([64,1,2,3,4,18,13],[2,34],[0,1]),([0,1,3,4,12,5,43],[17],[]),([135,0,1,2,3,4,5],[],[]),([64,2,3,31,4,5,18],[34],[0]),([0,1,136,3,4,12,5],[17],[]),([0,1,2,3,4,137,16],[2],[]),([0,1,2,31,12,15,5],[2,12,35],[0]),([0,1,3,12,15,5,16],[3,11,36],[0]),([0,1,139,2,3,4,5],[16],[]),([64,83,3,4,5,18],[2,12],[0]),([1,2,140,3,4,5,18],[1,27],[]),([0,1,3,4,87,5,16],[1],[1]),([71,0,1,3,4,5],[37],[]),([0,1,3,4,141,5,16],[2],[]),([1,49,2,3,4,5,18],[1],[0]),([0,1,142,3,4,5,16],[1],[1]),([20,0,1,2,3,4,18],[27],[]),([19,0,3,4,5],[2,8,12,32,38],[0]),([143,0,1,2,3,4,5],[],[]),([1,2,6,3,4,5,18],[1,12],[0]),([76,0,1,2,4,5,13],[1,39],[0]),([0,1,6,3,4,5,27],[12],[0]),([144,79,0,2,3,4,5],[40],[1]),([145,1,2,3,4,5,18],[1,41],[]),([146,0,1,2,3,51,5],[10,11,42],[]),([1,2,3,147,5,18],[2,12],[]),([0,1,148,2,3,4,5],[],[]),([0,1,6,3,4,81,5],[12],[]),([76,1,2,3,4,5,18],[],[0]),([0,6,3,4,8],[2,4,5,7,12],[0]),([70,1,2,3,4,5,18],[1],[0]),([1,2,3,12,18,24],[1,18,43,44],[0,1]),([1,149,2,3,4,5,18],[],[]),([0,1,150,3,4,5,16],[1,2],[]),([104,0,2,3,77,4,5],[],[]),([1,6,3,4,12,5,18],[12],[0]),([151,1,2,3,4,5,18],[1,27,45],[]),([146,0,1,2,4,5,13],[18,46],[]),([1,153,2,3,4,5,18],[],[]),([58,0,1,2,31,4,13],[1],[]),([20,0,1,2,3,4,5],[],[0]),([1,2,155,3,4,5,18],[1,12],[]),([0,1,2,3,4,5,52],[2,18,22],[0]),([69,1,2,3,4,18,24],[18,47],[0]),([76,0,1,31,57,4,5],[2],[]),([0,1,157,2,3,4,5],[],[]),([71,0,1,2,3,4,5],[],[]),([1,2,3,77,4,5,18],[1],[0,1]),([1,2,3,158,4,5],[12,18,48],[]),([1,2,6,3,4,18,13],[2],[0,1]),([74,0,1,2,3,4,5],[],[0]),([20,1,2,3,4,18],[27],[0,1]),([38,0,1,2,3,12,5],[17,49],[1]),([67,1,2,3,4,18,13],[1,34],[0]),([50,1,2,3,4,18,24],[1,44],[0]),([70,0,1,2,3,87,5],[12,22],[0]),([1,2,3,4,18,13,117],[2],[1]),([159,0,1,2,3,4,5],[],[]),([0,1,2,3,160,4,5],[18,27],[]),([162,0,1,2,3,5,21],[50],[]),([0,1,2,3,15,21,24],[11,12],[1]),([65,1,2,3,4,18,13],[1,2,34],[0]),([1,2,3,4,18,8],[2,12],[0]),([20,0,1,2,3,4,21],[1],[0]),([0,1,2,140,3,4,5],[1],[]),([0,1,3,4,12,16,13],[3],[0]),([102,1,2,6,3,4,5],[12],[]),([76,0,6,3,31,4,5],[2],[]),([0,1,164,2,3,4,5],[],[]),([0,1,2,3,165,4,5],[],[]),([0,1,153,2,3,4,5],[],[]),([146,0,1,2,31,15,5],[10],[]),([78,0,6,3,4,5,21],[2,12],[]),([20,62,0,1,3,4,5],[],[0]),([0,1,3,77,4,5,16],[1],[0]),([145,0,1,2,3,4,5],[1,22],[]),([0,67,2,3,4,5,59],[51],[0,1]),([76,0,1,3,77,4,5],[2,22],[1]),([73,0,1,2,3,4,5],[],[0]),([58,0,2,6,3,4,5],[2],[]),([1,2,3,4,8,11],[2,12],[0]),([0,1,2,3,55,4,5],[1,2,12,18,27],[0,1]),([1,2,3,4,5,8,11],[12],[0]),([104,76,0,2,3,4,5],[],[]),([20,1,2,6,3,4,18],[1],[0]),([0,6,3,4,5,8],[2,4,7,12],[0]),([0,1,2,3,4,5,43],[],[]),([0,1,2,3,15,5,27],[12,26],[]),([0,6,3,31,4,12,5],[3,10],[0]),([0,7,6,3,4,5,43],[7],[0]),([20,0,7,6,3,4,5],[7],[0]),([0,1,2,3,81,30,5],[12],[]),([0,1,49,2,4,15,5],[17],[]),([20,0,1,6,3,4,16],[1,2],[]),([78,0,1,6,3,4,5],[12],[0]),([166,0,1,2,3,4,5],[18,27],[]),([76,0,1,6,3,4,5],[12],[1]),([20,0,1,3,4,12,5],[17],[0]),([0,1,2,3,167,5,16],[52],[1]),([62,0,1,3,4,5,43],[],[]),([38,0,1,3,12,5,16],[17,36],[]),([0,1,168,2,3,4,5],[12],[]),([0,1,6,3,12,15,5],[3,11,12,53],[0]),([104,0,2,31,57,4,5],[12],[]),([58,0,2,3,31,4,21],[1],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_6_0 : checkNodesBT W_23 g_23 F_23 P_23_6 A_23 B_23_5 6 N_23_6_0 = true := by decide +kernel
def N_23_6_1 : List NodeSpec := [([58,0,1,2,3,4,21],[1],[0]),([1,2,3,4,18,13,59],[2],[0,1]),([152,169,1,2,3,4,5],[2,12],[]),([44,0,2,3,15,5,21],[],[]),([0,1,2,3,170,4,5],[],[]),([0,1,31,57,4,5,16],[],[0,1]),([0,1,2,3,171,4,5],[],[]),([0,1,3,172,4,5,16],[1,2],[]),([0,1,2,3,12,51,5],[2,12,54],[]),([35,0,1,2,3,5,24],[17],[0]),([0,1,2,3,81,5,24],[2,17],[0]),([0,1,2,3,12,5,34],[2],[]),([0,1,2,3,30,5,27],[12],[1]),([173,0,1,2,3,4,5],[],[]),([78,0,1,174,3,4,5],[55],[]),([58,0,1,2,57,4,5],[2],[]),([0,6,3,4,21,16],[1,2,12,56],[0,1]),([175,0,1,2,3,4,5],[26],[]),([0,1,2,3,176,4,5],[18,27],[]),([0,1,2,3,4,5,177],[39],[]),([0,1,2,3,75,4,5],[],[0]),([76,0,1,3,4,12,5],[17],[0]),([151,1,2,3,4,5],[2,12,45,57],[]),([50,0,1,2,3,4,5],[],[]),([0,1,2,3,32,4,5],[2,12],[0]),([0,1,2,3,12,21,24],[],[0,1]),([0,1,2,3,4,21,27],[12],[0,1]),([0,1,2,3,12,5,101],[2,18,49],[]),([0,67,2,31,4,5,13],[],[0]),([178,0,1,2,3,4,5],[],[]),([99,0,1,2,31,4,5],[12,18],[]),([1,2,3,82,4,5,18],[],[1]),([179,0,1,2,3,4,5],[],[]),([0,1,2,3,51,5,24],[1,12,18],[1]),([0,1,2,3,4,5,180],[],[]),([181,0,1,2,3,4,5],[26],[]),([44,48,0,1,2,15,5],[],[0]),([182,0,1,2,3,4,5],[18,22],[]),([183,0,1,2,3,4,5],[],[]),([50,0,1,3,4,5,27],[22],[0,1]),([0,184,2,3,4,5,27],[],[1]),([146,0,2,3,4,5,21],[1],[]),([71,0,1,3,4,5,59],[2],[]),([0,1,2,3,4,5,185],[],[0]),([0,1,2,3,42,5,21],[2,58],[0]),([186,0,1,2,3,4,5],[],[]),([35,0,1,2,3,21,24],[1,17],[]),([65,0,1,3,4,12,5],[17],[]),([0,1,2,3,54,4,5],[1,12],[0,1]),([187,0,1,2,3,4,5],[],[]),([188,0,1,2,3,4,5],[18,27],[]),([0,1,3,30,12,5,16],[12],[0]),([78,0,1,3,4,21,16],[1,2],[]),([58,0,1,2,3,4,59],[22],[0]),([0,1,2,3,4,5,189],[],[]),([191,0,1,2,3,4,5],[18,27],[]),([192,0,1,2,3,4,5],[],[]),([62,0,1,3,4,21,16],[],[0]),([86,0,1,2,3,4,5],[],[0]),([1,2,3,4,5,94,193],[2],[]),([0,1,2,3,15,5,137],[16],[]),([0,1,2,3,4,5,194],[],[]),([0,125,2,3,4,5,43],[59],[1]),([0,1,63,3,4,5,16],[],[0]),([0,1,2,3,4,94,21],[12],[0]),([196,0,1,2,3,4,5],[18,55],[]),([76,0,2,3,4,5,21],[1,39],[]),([0,1,2,3,4,5,46],[2],[0]),([0,1,2,3,122,30,5],[12],[]),([0,1,3,57,4,21,16],[2],[0,1]),([1,2,3,30,18,24],[1,12,18,44],[0,1]),([0,1,57,4,16,13],[1,2],[0,1]),([50,0,1,2,3,30,5],[],[0]),([0,184,2,3,4,5,16],[60],[]),([35,0,2,3,30,5,21],[12],[]),([65,0,1,57,4,5,13],[2,16],[0]),([197,0,1,2,3,4,5],[],[]),([65,0,1,3,4,5,117],[2,22],[1]),([35,0,1,2,3,5,34],[12,22],[0]),([198,0,1,2,3,4,5],[],[]),([104,0,49,2,3,4,5],[],[]),([0,1,2,3,4,5,59],[2],[0]),([0,1,2,3,4,5,199],[],[]),([0,1,49,3,4,5,16],[1],[0]),([44,0,2,3,4,21,16],[12],[1]),([44,0,1,2,15,5,13],[18,46],[1]),([152,0,1,3,4,5,16],[1,61],[]),([0,125,2,3,4,21,16],[1],[1]),([78,0,1,3,4,5,16],[1],[0]),([0,1,201,3,4,5,16],[1,12],[]),([38,39,1,2,3,4,5],[18],[0]),([0,1,2,3,202,4,5],[30],[]),([0,1,2,3,203,4,5],[],[]),([58,0,1,2,3,4,13],[16],[0]),([65,0,1,2,31,4,5],[12],[0]),([102,1,2,3,4,5,21],[24],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_6_1 : checkNodesBT W_23 g_23 F_23 P_23_6 A_23 B_23_5 6 N_23_6_1 = true := by decide +kernel
def N_23_6 := N_23_6_0 ++ N_23_6_1
def B_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_6
set_option maxRecDepth 500000 in
lemma B_23_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 6 xs.toFinset) B_23_6 := by
  have hP := buildPoolsSubBT_sound (pdepth := 8) (W := W_23) (raw := r_23) (pspecs := ps_23) (used := [1,2,3,4,5,7,8,10,11,12,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61]) S_23_ok
  have hm0 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_5_ok C_23_6_0
  have hm1 := checkNodesBT_mem (by decide) gp_23 W_23_ok hP A_23_ok B_23_5_ok C_23_6_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def P_23_7 : BT (Option BoundPool) := buildPoolsSubBT 8 W_23 r_23 S_23 ps_23 [1,2,3,7,10,11,12,16,17,18,22,24,26,27,30,34,36,39,41,44,46,47,49,55,56,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143]
def N_23_7 : List NodeSpec := [([99,0,1,2,3,4,5,13],[1,18,46],[0]),([65,0,1,2,3,4,5,13],[1,2,16],[0]),([50,0,1,2,3,4,5,24],[1,2,17,62],[0]),([50,0,1,2,3,4,5],[1,12,18,55,62,63],[0,1]),([69,0,1,2,3,4,5,24],[2,47,64,65],[0,1]),([0,67,1,2,3,4,5,13],[1,12,16,66],[0,1]),([0,1,2,3,4,5,101],[2,11,12,18,27,67],[0,1]),([102,1,2,3,4,5],[2,11,12,24,68],[0,1]),([35,0,1,2,3,4,5],[2,12,27,69],[0,1]),([38,0,1,2,3,4,5,16],[1,70,71,72],[0]),([38,0,1,2,3,4,5],[1,12,18,27,71,72],[0,1]),([0,1,2,3,4,15,5,21],[11,12,16,73],[0,1]),([78,0,1,2,3,4,5,21],[2,12,74],[0,1]),([0,1,2,3,4,5,21,59],[75,76],[0,1]),([144,0,1,2,3,4,5,16],[12,77],[0]),([0,1,2,3,4,5,21,43],[2,78],[0,1]),([204,0,1,2,3,4,5,21],[18,22,79,80],[]),([0,1,2,3,4,5,21,161],[12,18,81,82,83],[0,1]),([44,0,1,2,3,4,5,16],[1,2,12,71,84],[0,1]),([44,48,0,1,2,3,4,5],[2,12,85,86],[0]),([0,1,2,3,4,5,137],[2,12,27,84],[0,1]),([0,1,2,3,57,4,5,24],[2,18],[0,1]),([0,1,2,3,4,5,117],[2,12,55,87],[0,1]),([0,1,2,3,30,5,24],[12,88],[0,1]),([0,1,3,57,4,5,16],[2,87],[0,1]),([0,1,2,3,57,4,5,21],[2,12,76,87],[0,1]),([44,0,1,2,3,57,4,5],[2,12,86,89,90],[0,1]),([62,0,1,2,3,4,5,21],[1,2,12,73,91],[0,1]),([0,1,2,3,4,21,16],[1,2,12],[0,1]),([0,1,2,3,31,4,5,24],[12,18],[0,1]),([58,0,1,2,3,31,4,5],[1,12,92,93],[0]),([99,0,1,2,3,4,5],[2,11,12,18,27,94],[0,1]),([58,0,1,2,3,4,5],[1,2,18,27,92,93],[0,1]),([0,1,2,3,31,4,5,59],[2,93,95],[0,1]),([146,0,1,2,3,31,4,5],[10,12,96],[0]),([35,0,1,2,3,4,5,21],[1,12,83],[0]),([146,0,1,2,3,4,5],[1,2,12,18,26,27,97],[0,1]),([205,1,2,3,31,4,5],[2,12,93,98],[]),([78,0,1,2,3,4,5],[12,18,30,55,74,99],[0,1]),([104,0,2,3,31,4,5],[12,16,93,100,101],[0,1]),([0,1,2,3,4,51,5],[1,2,12,18],[0,1]),([0,1,6,3,4,5,16],[2,12,56],[0,1]),([0,1,2,3,4,5,59],[2,18,22,93,95],[0,1]),([64,0,2,3,4,5,21],[1,2,12,102],[0,1]),([206,0,1,2,6,3,4,5],[12,18,22,103],[]),([0,1,2,3,77,4,5],[1,2,22,26],[0,1]),([0,1,2,6,3,4,5],[1,2,12,22],[0,1]),([0,1,2,3,30,12,5],[2,12,104],[0,1]),([0,1,2,6,207,3,4,5],[2,12,18,105],[]),([0,1,2,3,147,5],[2,12,106,107],[0]),([0,1,2,6,3,31,4,5],[2,12],[0,1]),([104,0,1,2,3,57,4,5],[2,12,16,87,101],[0,1]),([44,1,2,3,4,5,18],[2,12,18,44,84],[1]),([0,1,6,3,4,12,5],[2,12],[0,1]),([0,1,2,6,3,4,5,13],[2,12],[0,1]),([0,1,2,3,4,8],[2,12,108],[0]),([0,1,2,3,4,21,24],[1,12],[0,1]),([0,1,2,3,4,5,94],[2,12,18,27,109,110],[0,1]),([64,83,0,3,4,5],[2,12],[0]),([0,1,2,3,45,4,5],[1,2,12,18],[0,1]),([0,1,2,3,4,5,8],[2,12,18,108,111],[0]),([0,1,2,3,208,4,5,21],[2,18,73,112],[]),([0,1,2,3,4,5,131],[12,16,27,102],[0,1]),([1,2,3,31,4,5,18],[2,12,18,34,93,113],[0,1]),([0,1,2,3,4,5,13,101],[18,114],[0,1]),([0,1,2,6,3,4,5,21],[1,2,12,115],[0]),([1,2,6,3,4,5,18],[2,12,18,115],[0,1]),([0,1,2,3,4,5,13,117],[2],[0,1]),([104,48,0,1,2,3,4,5],[2,12,101,116],[0,1]),([205,1,2,6,3,4,5],[2,12,115,117,118],[]),([104,0,2,6,3,4,5],[2,12,115],[0,1]),([64,1,2,3,4,5,18],[2,12,34,41,102],[0,1]),([44,0,1,2,3,4,5,13],[12,18,46],[0,1]),([0,1,2,3,57,4,30,5],[2,12,90,119],[0]),([1,2,3,57,4,5,18],[2,12,18,34,87],[0,1]),([20,0,1,2,3,4,5],[1,2,12,18,27,115],[0,1]),([7,1,2,3,4,5,18],[2,12,18,34,44,111],[0,1]),([62,0,1,6,3,4,5],[2,12],[0]),([0,1,2,6,3,4,5,18],[1,12,18,41,118],[0]),([62,1,2,3,4,5,18],[2,12,18,44,109],[0,1]),([44,0,2,3,4,5,21],[1,12,84],[0,1]),([209,1,2,3,4,5,18],[1,2,12,18,41],[1]),([0,1,2,3,15,5,24],[11,12,18,120],[0,1]),([0,1,63,2,3,4,5],[1,2,12,22],[0,1]),([0,1,210,2,3,4,5,16],[12,18,121,122,123],[1]),([0,125,1,2,3,4,5,16],[1,2,12,70,71,121,124],[0,1]),([0,1,2,3,31,4,12,5],[2,3,10,12],[0,1]),([1,2,3,4,18,13],[1,2,18,34,125],[0,1]),([0,1,2,6,3,77,4,5],[2],[0,1]),([0,1,2,3,4,5,21,34],[12,83,126],[0,1]),([44,0,1,2,3,15,5],[11,12,17,18,26,127],[0,1]),([70,0,1,2,3,4,5],[1,12,26,27],[0,1]),([0,1,2,3,12,15,5],[2,11,12,18],[0,1]),([70,0,1,2,6,3,4,5],[12,128],[0]),([152,0,1,2,3,4,5],[1,12,18,55,129,130],[0]),([0,1,2,3,4,5,43],[18,22,115],[0,1]),([64,0,1,2,3,4,5,13],[2,12,16],[0,1]),([152,1,2,3,4,5,18],[1,2,12,18,129,131],[0]),([0,1,2,6,3,4,5,43],[115],[0,1]),([0,1,2,3,31,4,5,21],[1,12,76],[0,1]),([64,0,1,2,3,4,5,16],[1,2,12,102],[0]),([20,0,1,2,6,3,4,5],[2,12,115],[0,1]),([0,1,2,6,3,4,15,5],[11,12,16,118],[0,1]),([0,7,6,3,4,5],[2,7,12,132,133],[0]),([0,1,2,3,82,4,5],[1,2,12,134],[0,1]),([0,1,2,3,31,4,51,5],[12,18,100],[0]),([0,1,3,4,12,5,16],[2,18,36,71,135],[0,1]),([64,0,2,3,31,4,5],[2,12,100],[0,1]),([65,0,1,2,3,4,5],[2,12,55,136],[0,1]),([0,1,49,2,3,4,5],[1,2,17,22],[0,1]),([0,1,2,3,31,77,4,5],[2,137],[0,1]),([76,0,1,2,3,4,5],[1,2,17,39,55],[0,1]),([76,0,1,2,3,31,4,5],[2,12,138],[0]),([0,1,2,3,4,5,13,59],[2,12,139],[0,1]),([0,1,2,3,105,4,5],[2,12,101,140,141],[0,1]),([0,1,136,2,3,4,5],[2,17,22,142],[0,1]),([0,1,2,3,31,4,5,16],[1,2,12,143],[0,1]),([62,0,1,3,4,5,16],[1,2,71,109],[0]),([0,1,2,3,12,5,24],[2,18,49,135],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_7 : checkNodesBT W_23 g_23 F_23 P_23_7 A_23 B_23_6 7 N_23_7 = true := by decide +kernel
def B_23_7 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_7
set_option maxRecDepth 500000 in
lemma B_23_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 7 xs.toFinset) B_23_7 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_6_ok C_23_7
def P_23_8 : BT (Option BoundPool) := buildPoolsSubBT 8 W_23 r_23 S_23 ps_23 [1,2,11,12,16,17,18,22,26,27,34,44,55,67,73,76,84,86,87,90,91,93,98,101,102,109,112,114,115,118,123,144,145,146,147,148,149,150]
def N_23_8 : List NodeSpec := [([0,1,2,3,4,5,13],[1,2,12,16,18,114],[0,1]),([0,1,210,2,3,4,5],[2,12,18,22,27,123],[0]),([0,1,2,3,4,15,5],[2,11,12,18,26,27,67,144],[0,1]),([0,1,2,3,4,5,21],[1,2,12,18,73,76,91],[0,1]),([1,2,3,4,5,18],[1,18,27,34,44],[0,1]),([64,0,1,2,3,4,5],[1,2,12,16,22,55,102,145],[0]),([0,1,2,3,31,4,5],[2,12,16,18,93,98],[0,1]),([0,1,2,3,4,5,18],[1,2,12,18,27],[0,1]),([205,1,2,3,4,5],[1,2,11,12,27],[0,1]),([0,1,2,3,57,4,5],[2,12,16,87,90,146],[0,1]),([0,7,1,2,3,4,5],[1,2,12,16,17,22,27,147],[0,1]),([0,1,2,6,3,4,5],[2,12,18,115,118],[0,1]),([104,0,1,2,3,4,5],[1,2,12,22,27,101,148],[0,1]),([0,1,2,3,208,4,5],[2,12,18,27,112],[0]),([62,0,1,2,3,4,5],[1,2,12,17,27,55,109,149],[0]),([44,0,1,2,3,4,5],[1,2,12,17,22,27,84,86,150],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_8 : checkNodesBT W_23 g_23 F_23 P_23_8 A_23 B_23_7 8 N_23_8 = true := by decide +kernel
def B_23_8 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_8
set_option maxRecDepth 500000 in
lemma B_23_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 8 xs.toFinset) B_23_8 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_7_ok C_23_8
def P_23_9 : BT (Option BoundPool) := buildPoolsSubBT 8 W_23 r_23 S_23 ps_23 [1,16,17,22,27,55]
def N_23_9 : List NodeSpec := [([0,1,2,3,4,5],[1,16,17,22,27,55],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_23_9 : checkNodesBT W_23 g_23 F_23 P_23_9 A_23 B_23_8 9 N_23_9 = true := by decide +kernel
def B_23_9 : BT (List (List Nat)) := buildBucketsBT W_23 N_23_9
set_option maxRecDepth 500000 in
lemma B_23_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_23 9 xs.toFinset) B_23_9 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok (buildPoolsSubBT_sound S_23_ok) A_23_ok B_23_8_ok C_23_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck r_23 g_23 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,2,34)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT B_23_9 r_23 = true := by decide +kernel
lemma low_23 : Lower r_23 g_23 10 := lower_of_forestBT root_23_ok B_23_9_ok root_23_in
def g_24 := 0xfffffffaffccf000fffffffaffccf000fffffffaffccf000fffffffaffccf000
def r_24 : List Nat := varsOf 63
set_option maxHeartbeats 0 in
lemma low_24 : Lower r_24 g_24 8 := by
  have hc : Lower (varsOf 62) 0xfffffff0ffccf000fffffff0ffccf000fffffff0ffccf000fffffff0ffccf000 7 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5)]) (by decide +kernel) low_8
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,32,33)]) (by decide +kernel) hc
def g_25 := 0xfffafc00fffafc00fffafc00fffafc00fffafc00fffafc00fffafc00fffafc00
def r_25 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_25 : Lower r_25 g_25 6 := by
  have hc : Lower (varsOf 30) 0xfff0fc00fff0fc00fff0fc00fff0fc00fff0fc00fff0fc00fff0fc00fff0fc00 5 := carry_of (swaps := [(0,4),(1,4),(2,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_26 := 0xfffef000fffef000fffef000fffef000fffef000fffef000fffef000fffef000
def r_26 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_26 : Lower r_26 g_26 6 := by
  have hc : Lower (varsOf 30) 0xfffcf000fffcf000fffcf000fffcf000fffcf000fffcf000fffcf000fffcf000 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_27 := 0xffeef000ffeef000ffeef000ffeef000ffeef000ffeef000ffeef000ffeef000
def r_27 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_27 : Lower r_27 g_27 5 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_28 := 0xfefefc00fefefc00fefefc00fefefc00fefefc00fefefc00fefefc00fefefc00
def r_28 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_28 : Lower r_28 g_28 5 := by
  have hc : Lower (varsOf 29) 0xfafaf000fafaf000fafaf000fafaf000fafaf000fafaf000fafaf000fafaf000 4 := carry_of (swaps := [(1,4),(3,4)]) (by decide +kernel) low_7
  exact lift_of_f (z := 2) (o := 0) (essPairs := [(VAR 1,8,10)]) (by decide +kernel) hc
def g_29 := 0xfffffac0fffffac0fffffac0fffffac0fffffac0fffffac0fffffac0fffffac0
def r_29 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_29 : Lower r_29 g_29 5 := lift_of_f (z := 16) (o := 0) (other := r_7) (G := g_7) (essPairs := [(VAR 4,0,16)]) (by decide +kernel) low_7
def g_30 := 0xfffffefeffccf000fffffefeffccf000fffffefeffccf000fffffefeffccf000
def r_30 : List Nat := varsOf 63
def p_30 : List Nat := [12,12,13,13,14,14,15,15,18,18,19,19,22,22,23,23,24,24,25,25,26,27,28,29,33,33,34,34,35,36,36,37,38,39,41,41,42,42,43,44,48,48,49,52,53,56]
def q_30 : List Nat := [8,4,9,5,10,6,11,7,16,2,17,3,20,6,21,7,16,8,17,9,10,11,20,21,32,1,32,2,3,32,4,5,6,7,40,9,40,10,11,40,32,16,17,20,21,40]
def F_30 : Nat := fullMask 46
set_option maxHeartbeats 0 in
lemma gp_30 : goodPairs g_30 p_30 q_30 := goodPairs_of (by decide +kernel)
def W_30 : BT Decor := buildWiresBT 5 (mkBase p_30 q_30 r_30) [(1,2,4),(1,3,5),(0,6,7),(1,4,5),(3,0,5),(1,10,4),(3,1,11),(3,1,9),(3,3,6),(1,0,6),(3,2,7),(1,10,1),(1,1,5),(1,0,4),(1,0,1)]
lemma W_30_ok : btAll (fun x => faithful p_30 q_30 x ∧ x.1 < 2^256) W_30 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_30 : List (List (Nat × Nat)) := [[]]
def A_30 : BT (List (Nat × Nat)) := btOfList 1 al_30
set_option maxHeartbeats 0 in
lemma A_30_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_30 = g_30) A_30 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_30_0 : Slice r_30 g_30 (subcubeFast 4 0) 6 := by
  have hc : Lower (varsOf 59) 0xffffeeeeffcc0000ffffeeeeffcc0000ffffeeeeffcc0000ffffeeeeffcc0000 6 := carry_of (swaps := [(1,2),(2,5),(3,5),(4,5)]) (by decide +kernel) low_25
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_1 : Slice r_30 g_30 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 55) 0xfffffefecccc0000fffffefecccc0000fffffefecccc0000fffffefecccc0000 6 := carry_of (swaps := [(1,2),(3,5),(4,5)]) (by decide +kernel) low_26
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_2 : Slice r_30 g_30 (subcubeFast 1 0) 6 := by
  have hc : Lower (varsOf 62) 0xfffffcfcffccf000fffffcfcffccf000fffffcfcffccf000fffffcfcffccf000 6 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_18
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_3 : Slice r_30 g_30 (subcubeFast 5 0) 5 := by
  have hc : Lower (varsOf 58) 0xffffccccffcc0000ffffccccffcc0000ffffccccffcc0000ffffccccffcc0000 5 := carry_of (swaps := [(0,4),(2,5),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 5) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_4 : Slice r_30 g_30 (subcubeFast 16 0) 5 := by
  have hc : Lower (varsOf 47) 0xfefefefef000f000fefefefef000f000fefefefef000f000fefefefef000f000 5 := carry_of (swaps := [(2,3),(4,5)]) (by decide +kernel) low_27
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_5 : Slice r_30 g_30 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 61) 0xfffffafaff00f000fffffafaff00f000fffffafaff00f000fffffafaff00f000 5 := carry_of (swaps := [(1,5),(2,5),(4,5)]) (by decide +kernel) low_28
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_6 : Slice r_30 g_30 (subcubeFast 0 1) 5 := by
  have hc : Lower (varsOf 62) 0xffffffffffccf000ffffffffffccf000ffffffffffccf000ffffffffffccf000 5 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,5),(4,5)]) (by decide +kernel) low_29
  exact slice_fast_direct_f (z := 0) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_7 : Slice r_30 g_30 (subcubeFast 32 1) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 32) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_8 : Slice r_30 g_30 (subcubeFast 17 0) 4 := by
  have hc : Lower (varsOf 46) 0xfcfcfcfcf000f000fcfcfcfcf000f000fcfcfcfcf000f000fcfcfcfcf000f000 4 := carry_of (swaps := [(0,4),(1,4),(3,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 17) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_30_9 : Slice r_30 g_30 (subcubeFast 18 0) 4 := by
  have hc : Lower (varsOf 45) 0xfafafafaf000f000fafafafaf000f000fafafafaf000f000fafafafaf000f000 4 := carry_of (swaps := [(1,4),(3,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 18) (o := 0) (by decide +kernel) hc
def S_30 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 4 0,6),some (subcubeFast 8 0,6),some (subcubeFast 1 0,6),some (subcubeFast 5 0,5),some (subcubeFast 16 0,5),some (subcubeFast 2 0,5),some (subcubeFast 0 1,5),some (subcubeFast 32 1,4),some (subcubeFast 17 0,4),some (subcubeFast 18 0,4)]
lemma S_30_ok : btAll (fun o => ∀ p, o = some p → Slice r_30 g_30 p.1 p.2) S_30 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_30_0) (forall_cons (fun _ h => by cases h; exact sl_30_1) (forall_cons (fun _ h => by cases h; exact sl_30_2) (forall_cons (fun _ h => by cases h; exact sl_30_3) (forall_cons (fun _ h => by cases h; exact sl_30_4) (forall_cons (fun _ h => by cases h; exact sl_30_5) (forall_cons (fun _ h => by cases h; exact sl_30_6) (forall_cons (fun _ h => by cases h; exact sl_30_7) (forall_cons (fun _ h => by cases h; exact sl_30_8) (forall_cons (fun _ h => by cases h; exact sl_30_9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
def ps_30 : BT (Option PoolSpec) := btOfList 5 ((([(7,[]),(5,[(1,2,4)]),(1,[(1,2,4),(1,0,6)]),(3,[]),(2,[]),(5,[]),(2,[(1,3,5)]),(0,[(1,3,5)]),(1,[]),(9,[]),(2,[(1,2,4)]),(1,[(1,2,4)]),(0,[]),(6,[]),(0,[(3,0,5)]),(8,[]),(1,[(1,0,1)]),(4,[(1,0,1)]),(0,[(1,0,1)]),(4,[])] : List PoolSpec)).map some)
def B_30_2 : BT (List (List Nat)) := BT.empty
lemma B_30_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_30 2 xs.toFinset) B_30_2 := .empty
def P_30_3 : BT (Option BoundPool) := buildPoolsSubBT 5 W_30 r_30 S_30 ps_30 []
def N_30_3 : List NodeSpec := [([0,1,8,9],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_30_3 : checkNodesBT W_30 g_30 F_30 P_30_3 A_30 B_30_2 3 N_30_3 = true := by decide +kernel
def B_30_3 : BT (List (List Nat)) := buildBucketsBT W_30 N_30_3
set_option maxRecDepth 500000 in
lemma B_30_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_30 3 xs.toFinset) B_30_3 :=
  buildBucketsBT_sound (by decide) gp_30 W_30_ok (buildPoolsSubBT_sound S_30_ok) A_30_ok B_30_2_ok C_30_3
def P_30_4 : BT (Option BoundPool) := buildPoolsSubBT 5 W_30 r_30 S_30 ps_30 []
def N_30_4 : List NodeSpec := [([0,1,4,8,5],[],[0]),([0,1,6,7,9],[],[0]),([1,3,11,6,5],[],[]),([12,2,3,4,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_30_4 : checkNodesBT W_30 g_30 F_30 P_30_4 A_30 B_30_3 4 N_30_4 = true := by decide +kernel
def B_30_4 : BT (List (List Nat)) := buildBucketsBT W_30 N_30_4
set_option maxRecDepth 500000 in
lemma B_30_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_30 4 xs.toFinset) B_30_4 :=
  buildBucketsBT_sound (by decide) gp_30 W_30_ok (buildPoolsSubBT_sound S_30_ok) A_30_ok B_30_3_ok C_30_4
def P_30_5 : BT (Option BoundPool) := buildPoolsSubBT 5 W_30 r_30 S_30 ps_30 [0,1,2,3]
def N_30_5 : List NodeSpec := [([13,0,2,3,4,5],[],[]),([0,1,2,4,7,9],[0],[0]),([0,1,3,6,5,9],[1],[0]),([0,1,4,6,5,7],[],[0]),([14,0,1,4,6,5],[],[]),([1,3,4,6,15,5],[2,3],[]),([10,1,3,4,6,5],[],[0]),([16,0,1,4,5,7],[],[]),([1,2,3,4,11,5],[],[0]),([1,17,2,3,4,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_30_5 : checkNodesBT W_30 g_30 F_30 P_30_5 A_30 B_30_4 5 N_30_5 = true := by decide +kernel
def B_30_5 : BT (List (List Nat)) := buildBucketsBT W_30 N_30_5
set_option maxRecDepth 500000 in
lemma B_30_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_30 5 xs.toFinset) B_30_5 :=
  buildBucketsBT_sound (by decide) gp_30 W_30_ok (buildPoolsSubBT_sound S_30_ok) A_30_ok B_30_4_ok C_30_5
def P_30_6 : BT (Option BoundPool) := buildPoolsSubBT 5 W_30 r_30 S_30 ps_30 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]
def N_30_6 : List NodeSpec := [([0,1,2,3,4,5,9],[0,4,5],[0]),([0,1,2,4,5,7],[0,6,7,8],[0]),([0,1,2,3,4,5,18],[0,4],[]),([0,1,3,4,6,5],[9,10,11,12],[0]),([10,1,2,3,4,5],[0,4,13,14],[0]),([1,2,3,4,19,5],[0,13,15],[]),([1,20,2,3,4,5],[0,4,9,16,17,18],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_30_6 : checkNodesBT W_30 g_30 F_30 P_30_6 A_30 B_30_5 6 N_30_6 = true := by decide +kernel
def B_30_6 : BT (List (List Nat)) := buildBucketsBT W_30 N_30_6
set_option maxRecDepth 500000 in
lemma B_30_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_30 6 xs.toFinset) B_30_6 :=
  buildBucketsBT_sound (by decide) gp_30 W_30_ok (buildPoolsSubBT_sound S_30_ok) A_30_ok B_30_5_ok C_30_6
def P_30_7 : BT (Option BoundPool) := buildPoolsSubBT 5 W_30 r_30 S_30 ps_30 [0,4,8,9,12,19]
def N_30_7 : List NodeSpec := [([0,1,2,3,4,5],[0,4,8,9,12,19],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_30_7 : checkNodesBT W_30 g_30 F_30 P_30_7 A_30 B_30_6 7 N_30_7 = true := by decide +kernel
def B_30_7 : BT (List (List Nat)) := buildBucketsBT W_30 N_30_7
set_option maxRecDepth 500000 in
lemma B_30_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_30 7 xs.toFinset) B_30_7 :=
  buildBucketsBT_sound (by decide) gp_30 W_30_ok (buildPoolsSubBT_sound S_30_ok) A_30_ok B_30_6_ok C_30_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_30_ok : forestRootCheck r_30 g_30 [(VAR 0,32,33),(VAR 1,16,18),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,2,18),(VAR 5,1,33)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_30_in : bucketContainsBT B_30_7 r_30 = true := by decide +kernel
lemma low_30 : Lower r_30 g_30 8 := lower_of_forestBT root_30_ok B_30_7_ok root_30_in
def g_31 := 0xfffffec0fffffec0fffffec0fffffec0fffffec0fffffec0fffffec0fffffec0
def r_31 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_31 : Lower r_31 g_31 6 := by
  have hc : Lower (varsOf 30) 0xfffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0fffffcc0 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_6
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,8,9)]) (by decide +kernel) hc
def g_32 := 0xffffffffffffffeefffefafaffccf000ffffffffffffffeefffefafaffccf000
def r_32 : List Nat := varsOf 127
def p_32 : List Nat := [12,12,13,13,14,14,15,15,18,18,19,19,22,22,23,23,24,24,25,25,26,27,28,29,33,33,35,35,36,36,37,38,38,39,41,41,43,43,44,46,49,49,50,50,52,52,53,56,56,58,65,65,66,66,67,69,69,70,70,71,72,72,73,74,75,76,80,80,81,84,84,85,96,96,98,100,104,106,112]
def q_32 : List Nat := [8,4,9,5,10,6,11,7,16,2,17,3,20,6,21,7,16,8,17,9,10,11,20,21,32,1,34,3,32,4,5,34,6,7,40,9,42,11,40,42,48,17,48,34,48,20,21,48,40,42,64,1,64,2,3,68,5,68,6,7,64,8,9,10,11,68,64,16,17,68,20,21,64,32,34,68,40,42,48]
def F_32 : Nat := fullMask 79
set_option maxHeartbeats 0 in
lemma gp_32 : goodPairs g_32 p_32 q_32 := goodPairs_of (by decide +kernel)
def W_32 : BT Decor := buildWiresBT 6 (mkBase p_32 q_32 r_32) [(1,4,5),(1,7,6),(3,1,8),(1,5,6),(3,0,10),(1,11,4),(3,1,12),(1,4,6),(3,1,14),(3,0,8),(1,15,5),(3,0,17),(0,7,6),(1,0,19),(1,1,19),(1,2,6),(1,3,19),(3,7,6),(1,24,5),(3,0,25),(3,4,6),(1,24,4),(2,7,6),(3,4,22),(3,1,28),(3,5,10),(3,5,14),(1,32,2),(3,4,10),(1,27,2)]
lemma W_32_ok : btAll (fun x => faithful p_32 q_32 x ∧ x.1 < 2^256) W_32 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_32 : List (List (Nat × Nat)) := [[]]
def A_32 : BT (List (Nat × Nat)) := btOfList 1 al_32
set_option maxHeartbeats 0 in
lemma A_32_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_32 = g_32) A_32 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_32_0 : Slice r_32 g_32 (subcubeFast 2 0) 9 := by
  have hc : Lower (varsOf 125) 0xffffffffffffffaafffafafaff00f000ffffffffffffffaafffafafaff00f000 9 := carry_of (swaps := [(1,6),(4,6),(5,6)]) (by decide +kernel) low_13
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_1 : Slice r_32 g_32 (subcubeFast 4 0) 9 := by
  have hc : Lower (varsOf 123) 0xffffffffffffffeeffeeaaaaffcc0000ffffffffffffffeeffeeaaaaffcc0000 9 := carry_of (swaps := [(0,2),(1,2),(2,6),(3,6),(5,6)]) (by decide +kernel) low_14
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_2 : Slice r_32 g_32 (subcubeFast 8 0) 9 := by
  have hc : Lower (varsOf 119) 0xffffffffffffeeeefefefafacccc0000ffffffffffffeeeefefefafacccc0000 9 := carry_of (swaps := [(0,1),(1,2),(3,6),(4,6),(5,6)]) (by decide +kernel) low_15
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_3 : Slice r_32 g_32 (subcubeFast 1 0) 9 := by
  have hc : Lower (varsOf 126) 0xffffffffffffffccfffcf0f0ffccf000ffffffffffffffccfffcf0f0ffccf000 9 := carry_of (swaps := [(0,6),(1,6),(2,3),(5,6)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_4 : Slice r_32 g_32 (identDom 0 1) 10 := by
  have hc : Lower (varsOf 125) 0xffffffffffffffaafffafafaffaaf000ffffffffffffffaafffafafaffaaf000 10 := carry_of (swaps := [(0,1),(1,6),(2,6),(4,6),(5,6)]) (by decide +kernel) low_23
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_5 : Slice r_32 g_32 (identDom 2 6) 9 := by
  have hc : Lower (varsOf 63) 0xfffefafafffcf0e0fffefafafffcf0e0fffefafafffcf0e0fffefafafffcf0e0 9 := carry_of (swaps := [(0,2),(1,2),(2,5),(3,5)]) (by decide +kernel) low_14
  exact slice_ident (u := 2) (v := 6) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_6 : Slice r_32 g_32 (subcubeFast 32 0) 8 := by
  have hc : Lower (varsOf 95) 0xffffffeeffffffeeffccf000ffccf000ffffffeeffffffeeffccf000ffccf000 8 := carry_of (swaps := [(1,2),(3,4),(5,6)]) (by decide +kernel) low_24
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_7 : Slice r_32 g_32 (subcubeFast 16 0) 8 := by
  have hc : Lower (varsOf 111) 0xffffffffffeeffeefafafafaf000f000ffffffffffeeffeefafafafaf000f000 8 := carry_of (swaps := [(0,1),(2,3),(4,6),(5,6)]) (by decide +kernel) low_30
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_8 : Slice r_32 g_32 (subcubeFast 34 0) 6 := by
  have hc : Lower (varsOf 93) 0xffffffaaffffffaaff00f000ff00f000ffffffaaffffffaaff00f000ff00f000 6 := carry_of (swaps := [(1,5),(2,5),(4,5),(5,6)]) (by decide +kernel) low_25
  exact slice_fast_direct_f (z := 34) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_9 : Slice r_32 g_32 (subcubeFast 32 4) 6 := by
  have hc : Lower (varsOf 91) 0xffffffeeffffffeeffccff00ffccff00ffffffeeffffffeeffccff00ffccff00 6 := carry_of (swaps := [(2,5),(3,4),(4,5),(5,6)]) (by decide +kernel) low_31
  exact slice_fast_direct_f (z := 32) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_10 : Slice r_32 g_32 (subcubeFast 36 0) 6 := by
  have hc : Lower (varsOf 91) 0xffffffeeffffffeeffcc0000ffcc0000ffffffeeffffffeeffcc0000ffcc0000 6 := carry_of (swaps := [(2,5),(3,5),(4,5),(5,6)]) (by decide +kernel) low_16
  exact slice_fast_direct_f (z := 36) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_11 : Slice r_32 g_32 (subcubeFast 20 0) 6 := by
  have hc : Lower (varsOf 107) 0xffffffffffeeffeeaaaaaaaa00000000ffffffffffeeffeeaaaaaaaa00000000 6 := carry_of (swaps := [(0,2),(1,2),(2,5),(3,5),(4,6)]) (by decide +kernel) low_26
  exact slice_fast_direct_f (z := 20) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_12 : Slice r_32 g_32 (subcubeFast 50 0) 4 := by
  have hc : Lower (varsOf 77) 0xffaaffaaffaaffaaf000f000f000f000ffaaffaaffaaffaaf000f000f000f000 4 := carry_of (swaps := [(1,4),(2,4),(3,4),(4,5),(5,6)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 50) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_13 : Slice r_32 g_32 (subcubeFast 82 0) 4 := by
  have hc : Lower (varsOf 45) 0xfafafafaf000f000fafafafaf000f000fafafafaf000f000fafafafaf000f000 4 := carry_of (swaps := [(1,4),(3,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 82) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_14 : Slice r_32 g_32 (subcubeFast 80 2) 4 := by
  have hc : Lower (varsOf 45) 0xfafafafaf000f000fafafafaf000f000fafafafaf000f000fafafafaf000f000 4 := carry_of (swaps := [(1,4),(3,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 80) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_15 : Slice r_32 g_32 (subcubeFast 96 1) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 96) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_32_16 : Slice r_32 g_32 (subcubeFast 49 0) 4 := by
  have hc : Lower (varsOf 78) 0xffccffccffccffccf000f000f000f000ffccffccffccffccf000f000f000f000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4),(4,5),(5,6)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 49) (o := 0) (by decide +kernel) hc
def S_32 : BT (Option (Nat × Nat)) := btOfList 5 [some (subcubeFast 2 0,9),some (subcubeFast 4 0,9),some (subcubeFast 8 0,9),some (subcubeFast 1 0,9),some (identDom 0 1,10),some (identDom 2 6,9),some (subcubeFast 32 0,8),some (subcubeFast 16 0,8),some (subcubeFast 34 0,6),some (subcubeFast 32 4,6),some (subcubeFast 36 0,6),some (subcubeFast 20 0,6),some (subcubeFast 50 0,4),some (subcubeFast 82 0,4),some (subcubeFast 80 2,4),some (subcubeFast 96 1,4),some (subcubeFast 49 0,4)]
lemma S_32_ok : btAll (fun o => ∀ p, o = some p → Slice r_32 g_32 p.1 p.2) S_32 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_32_0) (forall_cons (fun _ h => by cases h; exact sl_32_1) (forall_cons (fun _ h => by cases h; exact sl_32_2) (forall_cons (fun _ h => by cases h; exact sl_32_3) (forall_cons (fun _ h => by cases h; exact sl_32_4) (forall_cons (fun _ h => by cases h; exact sl_32_5) (forall_cons (fun _ h => by cases h; exact sl_32_6) (forall_cons (fun _ h => by cases h; exact sl_32_7) (forall_cons (fun _ h => by cases h; exact sl_32_8) (forall_cons (fun _ h => by cases h; exact sl_32_9) (forall_cons (fun _ h => by cases h; exact sl_32_10) (forall_cons (fun _ h => by cases h; exact sl_32_11) (forall_cons (fun _ h => by cases h; exact sl_32_12) (forall_cons (fun _ h => by cases h; exact sl_32_13) (forall_cons (fun _ h => by cases h; exact sl_32_14) (forall_cons (fun _ h => by cases h; exact sl_32_15) (forall_cons (fun _ h => by cases h; exact sl_32_16) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))
def ps_32 : BT (Option PoolSpec) := btOfList 8 ((([(2,[(1,4,5),(1,5,6),(0,7,6),(1,0,19)]),(3,[(1,4,5),(1,5,6),(0,7,6)]),(15,[]),(2,[(1,4,5),(1,4,6),(0,7,6),(1,1,19)]),(0,[(1,4,5),(1,4,6),(0,7,6)]),(13,[]),(14,[]),(0,[(1,4,5),(1,4,6),(0,7,6),(1,3,19)]),(6,[(1,2,6)]),(7,[(1,2,6)]),(3,[(1,5,6),(1,4,10),(3,1,8)]),(6,[(1,4,10),(3,1,8)]),(16,[]),(0,[(1,5,6),(3,0,10)]),(7,[(1,5,6),(3,0,10)]),(2,[(3,4,6),(1,27,5),(3,0,25)]),(3,[(1,4,6),(3,1,14)]),(6,[(1,4,6),(3,1,14)]),(3,[(1,2,6),(1,5,6)]),(0,[(1,2,6),(1,5,6)]),(8,[]),(2,[(1,4,5),(1,7,6),(3,0,8)]),(3,[(1,2,6),(1,4,5),(1,5,6)]),(2,[(1,2,6),(1,4,5),(1,5,6)]),(0,[(1,2,6),(1,4,5),(1,5,6)]),(9,[]),(7,[(1,2,6),(1,5,6)]),(2,[(1,2,6),(1,5,6),(3,0,10)]),(0,[(1,2,6),(1,5,6),(3,0,10)]),(9,[(3,0,10)]),(6,[(1,7,6),(3,1,8)]),(6,[]),(12,[]),(6,[(1,2,6),(3,0,10)]),(1,[(1,5,6),(3,0,10)]),(2,[(1,2,6),(1,4,6),(3,1,14)]),(1,[(1,4,6),(3,1,14)]),(3,[]),(0,[]),(0,[(1,4,6),(1,5,14),(3,0,8)]),(7,[(1,5,14),(3,0,8)]),(2,[(1,4,5),(1,5,6),(0,7,6)]),(2,[(3,5,6),(1,32,4),(3,1,28)]),(3,[(1,2,6),(1,5,6),(3,5,10)]),(0,[(1,2,6),(1,5,6),(3,5,10)]),(2,[(1,2,6),(1,5,6),(3,5,10)]),(10,[]),(3,[(1,2,6)]),(0,[(1,2,6)]),(2,[(1,4,5),(0,7,6),(1,0,19)]),(6,[(0,7,6),(1,0,19)]),(2,[(1,4,5),(1,4,6),(0,7,6)]),(0,[(1,4,5),(1,7,6),(3,0,8)]),(4,[(1,4,5),(1,7,6),(3,0,8)]),(0,[(1,4,5),(0,7,6),(1,3,19)]),(2,[(1,4,5),(1,7,6),(3,1,8)]),(2,[(1,4,5),(0,7,6),(1,1,19)]),(3,[(1,4,5),(1,7,6),(3,1,8)]),(4,[(1,4,5),(1,7,6),(3,1,8)]),(6,[(1,7,6),(3,0,8)]),(3,[(3,5,6),(1,32,4)]),(2,[(3,5,6),(1,32,4)]),(0,[(3,5,6),(1,32,4)]),(1,[(3,5,6),(1,32,4)]),(6,[(1,32,4)]),(3,[(1,2,6),(3,5,6)]),(0,[(1,2,6),(3,5,6)]),(2,[(1,2,6)]),(2,[(1,2,6),(3,5,6)]),(3,[(1,4,5),(1,5,6)]),(2,[(1,4,5),(1,5,6)]),(0,[(1,4,5),(1,5,6)]),(1,[(1,4,5),(1,5,6)]),(7,[(1,5,6)]),(2,[(1,2,6),(1,5,6)]),(3,[(1,4,6),(3,5,14)]),(0,[(1,4,6),(3,5,14)]),(1,[]),(2,[(1,4,6),(3,5,14)]),(6,[(1,4,6)]),(7,[(1,2,6),(3,5,6)]),(3,[(1,5,6),(1,4,10)]),(0,[(1,5,6)]),(6,[(1,4,10)]),(3,[(1,4,5),(1,4,6)]),(2,[(1,4,5),(1,4,6)]),(0,[(1,4,5),(1,4,6)]),(1,[(1,4,5),(1,4,6)]),(7,[]),(3,[(3,5,6),(1,32,2)]),(0,[(3,5,6),(1,32,2)]),(1,[(3,5,6)]),(2,[(3,5,6),(1,32,2)]),(7,[(3,5,6),(1,32,2)]),(6,[(1,32,2)]),(3,[(1,4,6)]),(3,[(1,4,5)]),(0,[(1,4,5)]),(6,[(1,7,6)]),(3,[(1,4,5),(1,7,6)]),(2,[(1,4,5),(1,7,6)]),(0,[(1,4,5),(1,7,6)]),(1,[(1,4,5),(1,7,6)]),(7,[(1,7,6)]),(3,[(1,4,6),(3,4,6)]),(0,[(1,4,6),(3,4,6)]),(2,[(1,4,6),(3,4,6)]),(3,[(1,5,6),(3,4,10)]),(0,[(1,5,6),(3,4,10)]),(1,[(1,5,6),(3,4,10)]),(2,[]),(2,[(1,5,6),(3,4,10)]),(3,[(1,5,6),(3,5,6)]),(0,[(1,5,6),(3,5,6)]),(2,[(1,5,6),(3,5,6)]),(1,[(1,5,6),(3,5,6)]),(3,[(1,2,6),(3,4,6)]),(0,[(1,2,6),(3,4,6)]),(2,[(1,2,6),(3,4,6)]),(11,[]),(3,[(1,2,6),(1,4,5)]),(2,[(1,2,6),(1,4,5)]),(0,[(1,2,6),(1,4,5)]),(1,[(1,4,5)]),(3,[(1,4,5),(2,7,6)]),(0,[(1,4,5),(2,7,6)]),(1,[(1,4,5),(2,7,6)]),(2,[(1,4,5),(2,7,6)]),(6,[(2,7,6)]),(3,[(1,4,5),(3,7,6)]),(0,[(1,4,5),(3,7,6)]),(5,[]),(2,[(1,4,5),(3,7,6)]),(6,[(3,7,6)]),(5,[(1,4,5)]),(2,[(1,4,6),(3,1,14)]),(0,[(1,4,6)]),(7,[(3,1,14)]),(3,[(1,2,6),(1,4,6)]),(2,[(1,2,6),(1,4,6)]),(0,[(1,2,6),(1,4,6)]),(1,[(1,4,6)]),(0,[(1,4,6),(1,5,14)]),(7,[(1,5,14)]),(3,[(1,2,6),(3,4,22)]),(0,[(1,2,6),(3,4,22)]),(2,[(1,2,6),(3,4,22)]),(1,[(3,4,22)]),(3,[(1,4,5),(0,7,6)]),(2,[(1,4,5),(0,7,6)]),(3,[(3,4,6),(1,27,2)]),(0,[(3,4,6),(1,27,2)]),(1,[(3,4,6)]),(2,[(3,4,6),(1,27,2)]),(7,[(1,27,2)]),(3,[(3,4,6),(1,27,5)]),(2,[(3,4,6),(1,27,5)]),(0,[(3,4,6),(1,27,5)]),(1,[(3,4,6),(1,27,5)]),(7,[(1,27,5)]),(2,[(1,5,6),(3,0,10)]),(6,[(3,0,10)]),(3,[(1,5,6)]),(3,[(3,5,6)]),(0,[(3,5,6)]),(2,[(3,5,6)]),(7,[(3,5,6)]),(1,[(1,5,6)]),(2,[(1,5,6)]),(3,[(3,4,6)]),(0,[(3,4,6)]),(2,[(3,4,6)]),(6,[(3,4,6)]),(2,[(1,4,6)]),(2,[(1,4,5)])] : List PoolSpec)).map some)
def B_32_5 : BT (List (List Nat)) := BT.empty
lemma B_32_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_32 5 xs.toFinset) B_32_5 := .empty
def P_32_6 : BT (Option BoundPool) := buildPoolsSubBT 8 W_32 r_32 S_32 ps_32 [0,1,2,3,4,5,6,7,8,9]
def N_32_6 : List NodeSpec := [([9,11,2,3,4,5,6],[],[]),([13,11,2,3,4,5,6],[],[]),([15,11,2,3,4,5,6],[],[]),([15,16,2,3,4,5,6],[],[]),([15,18,2,3,4,5,6],[],[]),([1,2,3,4,20,10],[0,1,2],[]),([0,2,3,5,21,14],[3,4,5],[]),([9,0,3,4,5,22,10],[],[]),([15,0,3,4,5,22,10],[],[]),([0,1,2,5,23,14],[6,7],[]),([11,1,3,4,7,22,10],[],[]),([0,1,3,7,22,14,10],[8,9],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_32_6 : checkNodesBT W_32 g_32 F_32 P_32_6 A_32 B_32_5 6 N_32_6 = true := by decide +kernel
def B_32_6 : BT (List (List Nat)) := buildBucketsBT W_32 N_32_6
set_option maxRecDepth 500000 in
lemma B_32_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_32 6 xs.toFinset) B_32_6 :=
  buildBucketsBT_sound (by decide) gp_32 W_32_ok (buildPoolsSubBT_sound S_32_ok) A_32_ok B_32_5_ok C_32_6
def P_32_7 : BT (Option BoundPool) := buildPoolsSubBT 8 W_32 r_32 S_32 ps_32 [1,2,5,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59]
def N_32_7 : List NodeSpec := [([9,0,2,3,4,5,6,10],[10,11],[0]),([11,1,2,3,4,5,6,8],[12,13],[0]),([11,1,2,3,4,12,5,6],[13,14],[0]),([26,1,2,3,4,5,6],[2,15],[]),([11,1,2,3,4,5,6,14],[13,14],[0]),([15,0,2,3,4,5,6,10],[16,17],[0]),([15,0,2,3,4,5,17,6],[16,17],[0]),([0,1,3,4,5,22,10,8],[2,5,18,19],[0]),([15,0,2,3,4,5,6,8],[16,20],[0]),([15,0,2,3,5,7,6,14],[5,17],[]),([16,1,2,3,4,5,6],[2,21],[]),([0,1,3,4,5,22,14,10],[5,8,9,19],[0]),([0,1,3,4,7,22,10],[2,8,22,23,24,25,26],[0]),([11,1,3,4,5,22,10],[2,18,27,28,29],[0]),([9,0,2,3,4,5,7,6],[30],[]),([0,1,2,3,28,5,7,6],[31,32],[]),([11,1,3,4,5,6,22],[18,27,33,34],[]),([15,0,3,4,5,6,22],[5,35,36],[0]),([29,0,1,3,4,5,6,22],[],[]),([0,1,2,3,4,5,6,8],[2,6,37,38],[]),([0,1,3,4,7,6,22,10],[5,26],[0]),([30,0,1,3,5,6,22,14],[9],[]),([16,1,2,3,4,5,6,14],[39,40],[0]),([0,1,2,3,4,19,10],[1,2,32,41],[0]),([31,0,2,3,4,5,6],[5,42],[]),([32,0,1,3,4,22,10],[2,5,43,44,45,46],[]),([0,1,3,4,5,6,22,8],[2,6,47,48],[]),([0,1,3,5,7,6,22,14],[5,8],[0]),([0,1,2,3,7,6,14,10],[5],[0]),([1,2,3,4,5,20,6],[5,49,50],[0]),([0,1,2,3,5,19,14],[5,32,51],[0]),([11,1,2,3,4,7,6,10],[2,14],[0]),([16,1,2,3,4,5,6,8],[37,52,53],[]),([0,1,2,4,5,23,6],[6,54],[0]),([9,0,2,3,4,5,6],[6,55],[]),([0,2,3,4,5,21,6],[5,56],[0]),([0,1,2,3,4,25,7,6],[31,32],[]),([9,0,2,3,4,5,6,8],[38,57,58],[]),([16,1,2,3,4,5,7,6],[59],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_32_7 : checkNodesBT W_32 g_32 F_32 P_32_7 A_32 B_32_6 7 N_32_7 = true := by decide +kernel
def B_32_7 : BT (List (List Nat)) := buildBucketsBT W_32 N_32_7
set_option maxRecDepth 500000 in
lemma B_32_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_32 7 xs.toFinset) B_32_7 :=
  buildBucketsBT_sound (by decide) gp_32 W_32_ok (buildPoolsSubBT_sound S_32_ok) A_32_ok B_32_6_ok C_32_7
def P_32_8 : BT (Option BoundPool) := buildPoolsSubBT 8 W_32 r_32 S_32 ps_32 [2,5,6,8,9,13,14,16,17,18,19,25,26,31,32,34,36,37,38,46,47,48,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162]
def N_32_8 : List NodeSpec := [([0,1,2,3,4,28,5,6],[5,60,61,62,63,64],[0]),([32,0,1,3,4,5,6,22],[5,8,9,46,47,48,65,66,67,68],[0]),([0,1,2,3,4,7,6,10],[2,31,32,69,70,71,72,73],[0]),([0,1,3,4,5,22,10],[2,8,18,19,25,26,74],[0]),([33,0,1,2,3,4,5,6],[5,25,37,38,75,76,77,78,79],[]),([32,0,1,3,4,5,22],[5,8,25,46,65,66,68,80],[0]),([0,1,2,3,4,5,6,10,8],[2,5,32,81,82,83],[0]),([0,1,2,3,5,7,6,14],[5,32,79,84,85,86,87,88],[0]),([32,0,1,34,3,4,5,6],[5,77,89,90,91,92,93,94],[]),([0,1,2,3,4,5,6,14,10],[2,5,73,79,82,95],[0]),([0,1,2,3,4,5,7,6,8],[2,5,32,96,97,98],[0]),([0,1,2,3,4,5,6,8],[2,5,32,98,99,100,101,102,103],[0]),([27,0,1,2,3,5,6,14],[2,5,88,104,105,106],[]),([0,1,3,4,5,6,22,10],[2,8,18,19,25,26,74],[0]),([35,0,1,2,3,4,5,6],[2,37,38,73,77,107,108,109,110,111],[]),([32,0,1,2,3,4,6,10],[2,5,31,112,113,114,115],[0]),([27,0,1,3,4,5,6,22],[2,5,9,47,48,67,116,117,118,119],[]),([0,1,3,4,5,7,6,22],[5,8,9,25,120,121,122,123],[0]),([29,0,1,2,3,4,5,6],[32,37,38,77,88,110,124,125,126,127,128],[0]),([24,0,1,2,3,4,5,6],[5,37,38,77,129,130,131,132,133],[]),([24,0,1,2,3,4,5,7,6],[32,123,133,134],[0]),([15,0,2,3,4,5,6],[5,16,17,36,135,136,137],[0]),([15,0,2,3,4,5,6,14],[5,16,17,36,135,136,137],[0]),([0,1,3,4,5,6,22,14],[5,8,9,138,139,140,141],[0]),([0,1,2,3,4,5,6,14,8],[2,6,32,95,142,143],[0]),([30,0,1,3,4,5,6,22],[9,25,47,48,67,144,145,146,147],[0]),([0,1,2,3,4,5,19,6],[5,31,32,37,38,77,88,131,148,149],[0]),([27,0,1,36,3,4,5,6],[2,5,77,150,151,152,153,154],[]),([0,1,2,3,4,5,25,6],[2,155,156,157,158,159],[0]),([11,1,2,3,4,5,6],[2,13,14,34,160,161],[0]),([11,1,2,3,4,5,6,10],[2,13,14,34,160,161,162],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_32_8 : checkNodesBT W_32 g_32 F_32 P_32_8 A_32 B_32_7 8 N_32_8 = true := by decide +kernel
def B_32_8 : BT (List (List Nat)) := buildBucketsBT W_32 N_32_8
set_option maxRecDepth 500000 in
lemma B_32_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_32 8 xs.toFinset) B_32_8 :=
  buildBucketsBT_sound (by decide) gp_32 W_32_ok (buildPoolsSubBT_sound S_32_ok) A_32_ok B_32_7_ok C_32_8
def P_32_9 : BT (Option BoundPool) := buildPoolsSubBT 8 W_32 r_32 S_32 ps_32 [2,5,8,9,25,31,32,37,38,47,48,67,73,77,79,82,88,91,95,96,97,110,123,131,136,141,152,162,163,164,165,166,167,168,169,170,171,172,173,174]
def N_32_9 : List NodeSpec := [([32,0,1,2,3,4,5,6],[5,31,37,38,77,88,91,110,131,163,164,165,166],[0]),([0,1,2,3,4,5,6,10],[2,31,73,82,162,167,168],[0]),([27,0,1,2,3,4,5,6],[2,31,37,38,77,88,110,131,152,169,170,171,172],[0]),([0,1,2,3,4,5,6,14],[5,79,88,95,136,141,173],[0]),([0,1,2,3,4,5,7,6],[31,32,88,96,97,123,174],[0]),([0,1,3,4,5,6,22],[8,9,25,47,48,67,77],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_32_9 : checkNodesBT W_32 g_32 F_32 P_32_9 A_32 B_32_8 9 N_32_9 = true := by decide +kernel
def B_32_9 : BT (List (List Nat)) := buildBucketsBT W_32 N_32_9
set_option maxRecDepth 500000 in
lemma B_32_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_32 9 xs.toFinset) B_32_9 :=
  buildBucketsBT_sound (by decide) gp_32 W_32_ok (buildPoolsSubBT_sound S_32_ok) A_32_ok B_32_8_ok C_32_9
def P_32_10 : BT (Option BoundPool) := buildPoolsSubBT 8 W_32 r_32 S_32 ps_32 [31,37,38,77,88,110]
def N_32_10 : List NodeSpec := [([0,1,2,3,4,5,6],[31,37,38,77,88,110],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_32_10 : checkNodesBT W_32 g_32 F_32 P_32_10 A_32 B_32_9 10 N_32_10 = true := by decide +kernel
def B_32_10 : BT (List (List Nat)) := buildBucketsBT W_32 N_32_10
set_option maxRecDepth 500000 in
lemma B_32_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_32 10 xs.toFinset) B_32_10 :=
  buildBucketsBT_sound (by decide) gp_32 W_32_ok (buildPoolsSubBT_sound S_32_ok) A_32_ok B_32_9_ok C_32_10
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_32_ok : forestRootCheck r_32 g_32 [(VAR 0,32,33),(VAR 1,16,18),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,2,18),(VAR 5,1,33),(VAR 6,1,65)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_32_in : bucketContainsBT B_32_10 r_32 = true := by decide +kernel
lemma low_32 : Lower r_32 g_32 11 := lower_of_forestBT root_32_ok B_32_10_ok root_32_in
def g_33 := 0xfffffffefffceac0fffffffefffceac0fffffffefffceac0fffffffefffceac0
def r_33 : List Nat := varsOf 63
def p_33 : List Nat := [6,6,7,7,9,9,11,11,13,13,14,14,18,18,19,19,20,20,21,21,24,24,25,26,28,33,33,34,34,35,36,36,37,40,40,42,44,48,48,49]
def q_33 : List Nat := [4,2,5,3,8,1,10,3,12,5,12,10,16,2,17,3,16,4,17,5,16,8,17,10,12,32,1,32,2,3,32,4,5,32,8,10,12,32,16,17]
def F_33 : Nat := fullMask 40
set_option maxHeartbeats 0 in
lemma gp_33 : goodPairs g_33 p_33 q_33 := goodPairs_of (by decide +kernel)
def W_33 : BT Decor := buildWiresBT 4 (mkBase p_33 q_33 r_33) [(1,1,5),(3,2,6),(1,2,5),(3,1,8),(1,1,2),(1,10,5)]
lemma W_33_ok : btAll (fun x => faithful p_33 q_33 x ∧ x.1 < 2^256) W_33 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_33 : List (List (Nat × Nat)) := [[],[(1,2)]]
def A_33 : BT (List (Nat × Nat)) := btOfList 1 al_33
set_option maxHeartbeats 0 in
lemma A_33_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_33 = g_33) A_33 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_33_0 : Slice r_33 g_33 (subcubeFast 1 0) 8 := by
  have hc : Lower (varsOf 62) 0xfffffffcfffcc0c0fffffffcfffcc0c0fffffffcfffcc0c0fffffffcfffcc0c0 8 := carry_of (swaps := [(0,5),(3,5),(4,5)]) (by decide +kernel) low_4
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_1 : Slice r_33 g_33 (subcubeFast 8 0) 8 := by
  have hc : Lower (varsOf 55) 0xfffffefefcfcc0c0fffffefefcfcc0c0fffffefefcfcc0c0fffffefefcfcc0c0 8 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_21
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_2 : Slice r_33 g_33 (subcubeFast 16 0) 8 := by
  have hc : Lower (varsOf 47) 0xfffefffeeac0eac0fffefffeeac0eac0fffefffeeac0eac0fffefffeeac0eac0 8 := carry_of (swaps := [(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_3 : Slice r_33 g_33 (subcubeFast 2 0) 7 := by
  have hc : Lower (varsOf 61) 0xfffffffafff0aa00fffffffafff0aa00fffffffafff0aa00fffffffafff0aa00 7 := carry_of (swaps := [(1,5),(2,5),(4,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_4 : Slice r_33 g_33 (subcubeFast 4 0) 7 := by
  have hc : Lower (varsOf 59) 0xffffffeeffccaa00ffffffeeffccaa00ffffffeeffccaa00ffffffeeffccaa00 7 := carry_of (swaps := [(2,5),(4,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_33_5 : Slice r_33 g_33 (subcubeFast 32 0) 7 := by
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) low_9
set_option maxHeartbeats 0 in
lemma sl_33_6 : Slice r_33 g_33 (subcubeFast 7 0) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000ffffff00ff000000ffffff00ff000000ffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 7) (o := 0) (by decide +kernel) hc
def S_33 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,8),some (subcubeFast 8 0,8),some (subcubeFast 16 0,8),some (subcubeFast 2 0,7),some (subcubeFast 4 0,7),some (subcubeFast 32 0,7),some (subcubeFast 7 0,4)]
lemma S_33_ok : btAll (fun o => ∀ p, o = some p → Slice r_33 g_33 p.1 p.2) S_33 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_33_0) (forall_cons (fun _ h => by cases h; exact sl_33_1) (forall_cons (fun _ h => by cases h; exact sl_33_2) (forall_cons (fun _ h => by cases h; exact sl_33_3) (forall_cons (fun _ h => by cases h; exact sl_33_4) (forall_cons (fun _ h => by cases h; exact sl_33_5) (forall_cons (fun _ h => by cases h; exact sl_33_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_33 : BT (Option PoolSpec) := btOfList 6 ((([(4,[]),(5,[]),(0,[]),(6,[]),(3,[]),(0,[(1,2,1),(1,2,5),(1,1,5)]),(2,[(1,2,1),(1,2,5),(1,1,5)]),(1,[(1,2,1),(1,2,5),(1,1,5)]),(4,[(1,1,5)]),(3,[(3,2,6)]),(0,[(1,1,5),(3,2,6)]),(1,[]),(1,[(1,1,5),(3,2,6)]),(2,[]),(2,[(1,1,5),(3,2,6)]),(5,[(3,2,6)]),(0,[(1,1,5),(1,2,5)]),(2,[(1,1,5),(1,2,5)]),(3,[(1,2,5)]),(1,[(1,1,5),(1,2,5)]),(3,[(1,2,6)]),(2,[(1,1,2),(1,10,5)]),(0,[(1,1,2),(1,10,5)]),(3,[(1,10,5)]),(4,[(1,10,5)]),(1,[(1,1,2),(1,10,5)]),(5,[(1,1,2)]),(0,[(1,2,1),(1,2,5)]),(2,[(1,2,1),(1,2,5)]),(5,[(1,2,1)]),(1,[(1,2,1),(1,2,5)]),(0,[(1,1,5)]),(2,[(1,1,5)]),(1,[(1,1,5)]),(0,[(1,1,2)]),(2,[(1,1,2)]),(1,[(1,1,2)])] : List PoolSpec)).map some)
def B_33_4 : BT (List (List Nat)) := BT.empty
lemma B_33_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_33 4 xs.toFinset) B_33_4 := .empty
def P_33_5 : BT (Option BoundPool) := buildPoolsSubBT 6 W_33 r_33 S_33 ps_33 []
def N_33_5 : List NodeSpec := [([7,9,0,3,4,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_33_5 : checkNodesBT W_33 g_33 F_33 P_33_5 A_33 B_33_4 5 N_33_5 = true := by decide +kernel
def B_33_5 : BT (List (List Nat)) := buildBucketsBT W_33 N_33_5
set_option maxRecDepth 500000 in
lemma B_33_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_33 5 xs.toFinset) B_33_5 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok (buildPoolsSubBT_sound S_33_ok) A_33_ok B_33_4_ok C_33_5
def P_33_6 : BT (Option BoundPool) := buildPoolsSubBT 6 W_33 r_33 S_33 ps_33 [0,1,2,3,4,5,6,7,8]
def N_33_6 : List NodeSpec := [([7,0,1,3,4,5,8],[0],[0]),([7,0,1,3,4,6,8],[0,1],[]),([7,0,1,3,4,5,11],[2,3],[0]),([7,0,10,3,4,5,6],[0,4],[]),([0,10,3,4,6,8],[0,1,4,5,6,7,8],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_33_6 : checkNodesBT W_33 g_33 F_33 P_33_6 A_33 B_33_5 6 N_33_6 = true := by decide +kernel
def B_33_6 : BT (List (List Nat)) := buildBucketsBT W_33 N_33_6
set_option maxRecDepth 500000 in
lemma B_33_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_33 6 xs.toFinset) B_33_6 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok (buildPoolsSubBT_sound S_33_ok) A_33_ok B_33_5_ok C_33_6
def P_33_7 : BT (Option BoundPool) := buildPoolsSubBT 6 W_33 r_33 S_33 ps_33 [0,1,2,3,4,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
def N_33_7 : List NodeSpec := [([7,0,1,2,3,4,5,6],[0,1,4,8,9],[0]),([7,0,1,2,3,4,5],[2,4,8,9,10,11,12,13,14,15],[0]),([0,1,2,3,4,6,8],[1,8,16,17,18,19],[0,1]),([0,1,2,3,4,5,6,11],[3,8,20],[0,1]),([0,1,2,3,4,5,11],[2,3,11,21,22,23,24,25,26],[0,1]),([0,1,10,3,4,5,8],[0,3,18,27,28,29,30],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_33_7 : checkNodesBT W_33 g_33 F_33 P_33_7 A_33 B_33_6 7 N_33_7 = true := by decide +kernel
def B_33_7 : BT (List (List Nat)) := buildBucketsBT W_33 N_33_7
set_option maxRecDepth 500000 in
lemma B_33_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_33 7 xs.toFinset) B_33_7 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok (buildPoolsSubBT_sound S_33_ok) A_33_ok B_33_6_ok C_33_7
def P_33_8 : BT (Option BoundPool) := buildPoolsSubBT 6 W_33 r_33 S_33 ps_33 [0,1,3,4,8,11,26,31,32,33,34,35,36]
def N_33_8 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,4,8,31,32,33],[0,1]),([0,1,2,10,3,4,5],[0,1,3,4,11,26,34,35,36],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_33_8 : checkNodesBT W_33 g_33 F_33 P_33_8 A_33 B_33_7 8 N_33_8 = true := by decide +kernel
def B_33_8 : BT (List (List Nat)) := buildBucketsBT W_33 N_33_8
set_option maxRecDepth 500000 in
lemma B_33_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_33 8 xs.toFinset) B_33_8 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok (buildPoolsSubBT_sound S_33_ok) A_33_ok B_33_7_ok C_33_8
def P_33_9 : BT (Option BoundPool) := buildPoolsSubBT 6 W_33 r_33 S_33 ps_33 [0,1,2,4,11,13]
def N_33_9 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,4,11,13],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_33_9 : checkNodesBT W_33 g_33 F_33 P_33_9 A_33 B_33_8 9 N_33_9 = true := by decide +kernel
def B_33_9 : BT (List (List Nat)) := buildBucketsBT W_33 N_33_9
set_option maxRecDepth 500000 in
lemma B_33_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_33 9 xs.toFinset) B_33_9 :=
  buildBucketsBT_sound (by decide) gp_33 W_33_ok (buildPoolsSubBT_sound S_33_ok) A_33_ok B_33_8_ok C_33_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_33_ok : forestRootCheck r_33 g_33 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9),(VAR 4,2,18),(VAR 5,1,33)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_33_in : bucketContainsBT B_33_9 r_33 = true := by decide +kernel
lemma low_33 : Lower r_33 g_33 10 := lower_of_forestBT root_33_ok B_33_9_ok root_33_in
def g_34 := 0xfffffffefefafc00fffffffefefafc00fffffffefefafc00fffffffefefafc00
def r_34 : List Nat := varsOf 63
def p_34 : List Nat := [10,10,11,11,12,12,13,13,14,15,17,17,19,19,20,20,21,22,22,23,25,25,26,26,28,33,33,34,34,35,36,36,37,38,39,40,40,41,48,48,50,56]
def q_34 : List Nat := [8,2,9,3,8,4,9,5,6,7,16,1,18,3,16,4,5,18,6,7,24,9,24,18,24,32,1,32,2,3,32,4,5,6,7,32,8,9,32,16,18,24]
def F_34 : Nat := fullMask 42
set_option maxHeartbeats 0 in
lemma gp_34 : goodPairs g_34 p_34 q_34 := goodPairs_of (by decide +kernel)
def W_34 : BT Decor := buildWiresBT 8 (mkBase p_34 q_34 r_34) [(1,3,5),(0,4,6),(1,3,4),(1,8,5),(3,7,9),(0,3,5),(1,2,11),(1,1,11),(0,8,5),(1,2,14),(1,0,15),(1,1,15),(1,4,5),(0,1,6),(1,19,2),(1,20,14),(0,3,4),(3,22,9),(3,22,8),(0,24,5),(1,24,5),(3,25,26),(1,25,2),(3,14,6),(3,3,5),(3,30,4),(2,3,5),(0,30,4),(1,30,4),(3,33,34),(1,33,2),(1,33,0),(2,4,5),(3,4,5),(0,39,3),(1,38,40),(1,39,3),(0,4,5),(3,43,18),(3,1,6),(3,4,6),(2,4,6),(1,47,11),(3,43,9),(0,3,18),(1,1,4),(1,3,51),(1,52,5),(3,1,53),(1,0,3),(1,4,55),(1,56,5),(3,0,57),(3,11,6),(2,59,4),(3,59,4),(1,44,3),(3,2,62),(3,0,62),(0,44,3),(1,2,43),(3,66,9),(1,0,43),(0,8,6),(2,3,18),(3,3,18),(0,0,18),(1,1,5),(0,52,73),(1,0,14),(3,14,9),(1,4,14),(3,2,9),(2,78,1),(2,78,0),(2,0,14),(3,1,62),(2,0,15),(1,22,5),(2,8,84),(3,24,5),(2,45,14),(2,8,5),(3,8,5),(1,89,22),(0,52,5),(1,2,91),(1,72,2),(3,14,18),(0,56,5),(1,1,95),(3,0,4),(1,97,3),(0,98,5),(1,1,99),(1,2,95),(1,19,14),(3,68,9),(3,1,5),(0,104,8),(1,105,2),(3,51,5),(3,1,3),(1,107,108),(3,20,9),(1,108,4),(0,111,5),(1,2,112),(1,25,1),(2,4,3),(1,115,45),(2,116,2),(1,47,13),(0,8,73),(1,40,2),(1,2,99),(1,40,1),(3,0,34),(3,68,18),(3,0,18),(1,125,3),(3,1,126),(0,1,42),(1,128,2),(3,44,3),(3,40,42),(3,39,3),(3,2,126),(3,2,57),(3,1,8),(1,135,5),(1,107,4),(1,98,5),(3,2,138),(1,0,4),(1,0,5),(3,140,141),(1,142,4),(1,143,3),(3,1,144),(0,8,141),(3,0,5),(0,147,8),(1,148,1),(1,147,3),(3,1,150),(3,1,18),(1,152,3),(3,0,137),(3,97,5),(1,155,3),(3,1,156),(0,8,84),(3,108,6),(0,78,0),(1,142,3),(3,1,161),(1,107,3),(1,0,1),(3,164,5),(1,165,0),(1,165,1),(3,1,57),(3,4,141),(3,108,18),(3,1,141),(3,0,73),(1,1,3),(3,173,73),(1,174,3),(1,175,4),(3,2,176),(1,39,55),(3,1,178),(1,30,1),(3,97,143),(3,1,138),(1,169,3),(3,1,183),(3,19,9),(2,45,43),(0,0,9),(0,0,34),(3,1,34),(1,30,0),(2,180,4),(1,38,3),(1,39,0),(3,51,6),(1,45,4),(2,45,0),(1,45,0),(1,107,1),(1,108,5),(2,175,4),(2,8,73),(3,4,199),(3,140,6),(1,39,108),(1,55,5),(3,97,18),(1,164,5),(3,4,73),(1,208,3),(2,3,4),(1,210,5),(2,98,5),(3,43,6),(3,4,205),(1,173,5),(3,4,215),(3,115,5),(3,1,205),(2,56,5),(3,45,4),(3,115,18),(1,46,0),(1,51,5),(3,8,141),(3,0,56),(3,225,5),(1,39,173),(1,140,5),(3,52,5),(2,190,4),(3,111,5),(1,89,0),(3,97,6),(3,38,8),(1,88,0),(3,147,8),(1,71,0),(3,210,5),(2,150,4),(1,32,4),(1,38,11),(3,0,205),(3,22,5),(3,43,3)]
lemma W_34_ok : btAll (fun x => faithful p_34 q_34 x ∧ x.1 < 2^256) W_34 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_34 : List (List (Nat × Nat)) := [[],[(0,1),(3,4)]]
def A_34 : BT (List (Nat × Nat)) := btOfList 1 al_34
set_option maxHeartbeats 0 in
lemma A_34_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_34 = g_34) A_34 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_34_0 : Slice r_34 g_34 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 59) 0xffffffeeeeaacc00ffffffeeeeaacc00ffffffeeeeaacc00ffffffeeeeaacc00 8 := carry_of (swaps := [(2,5),(3,5),(4,5)]) (by decide +kernel) low_2
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_1 : Slice r_34 g_34 (identDom 0 3) 8 := by
  have hc : Lower (varsOf 55) 0xfffffefefafaa8a8fffffefefafaa8a8fffffefefafaa8a8fffffefefafaa8a8 8 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,5),(4,5)]) (by decide +kernel) low_4
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_2 : Slice r_34 g_34 (identDom 1 4) 8 := by
  have hc : Lower (varsOf 47) 0xfffefffefcc8fcc8fffefffefcc8fcc8fffefffefcc8fcc8fffefffefcc8fcc8 8 := carry_of (swaps := [(1,3),(2,3),(4,5)]) (by decide +kernel) low_4
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_3 : Slice r_34 g_34 (subcubeFast 1 0) 7 := by
  have hc : Lower (varsOf 62) 0xfffffffcfcf0fc00fffffffcfcf0fc00fffffffcfcf0fc00fffffffcfcf0fc00 7 := carry_of (swaps := [(0,5),(1,5),(4,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_4 : Slice r_34 g_34 (subcubeFast 2 0) 7 := by
  have hc : Lower (varsOf 61) 0xfffffffafafaf000fffffffafafaf000fffffffafafaf000fffffffafafaf000 7 := carry_of (swaps := [(1,5),(3,5),(4,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_5 : Slice r_34 g_34 (subcubeFast 11 0) 4 := by
  have hc : Lower (varsOf 52) 0xfffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 11) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_6 : Slice r_34 g_34 (subcubeFast 19 0) 4 := by
  have hc : Lower (varsOf 44) 0xfff0fff0f000f000fff0fff0f000f000fff0fff0f000f000fff0fff0f000f000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 19) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_7 : Slice r_34 g_34 (subcubeFast 21 0) 4 := by
  have hc : Lower (varsOf 42) 0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00 4 := carry_of (swaps := [(0,3),(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 21) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_34_8 : Slice r_34 g_34 (subcubeFast 14 0) 4 := by
  have hc : Lower (varsOf 49) 0xffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000ffffaaaaaaaa0000 4 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 14) (o := 0) (by decide +kernel) hc
def S_34 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 4 0,8),some (identDom 0 3,8),some (identDom 1 4,8),some (subcubeFast 1 0,7),some (subcubeFast 2 0,7),some (subcubeFast 11 0,4),some (subcubeFast 19 0,4),some (subcubeFast 21 0,4),some (subcubeFast 14 0,4)]
lemma S_34_ok : btAll (fun o => ∀ p, o = some p → Slice r_34 g_34 p.1 p.2) S_34 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_34_0) (forall_cons (fun _ h => by cases h; exact sl_34_1) (forall_cons (fun _ h => by cases h; exact sl_34_2) (forall_cons (fun _ h => by cases h; exact sl_34_3) (forall_cons (fun _ h => by cases h; exact sl_34_4) (forall_cons (fun _ h => by cases h; exact sl_34_5) (forall_cons (fun _ h => by cases h; exact sl_34_6) (forall_cons (fun _ h => by cases h; exact sl_34_7) (forall_cons (fun _ h => by cases h; exact sl_34_8) (fun _ h => (List.not_mem_nil h).elim))))))))))
def ps_34 : BT (Option PoolSpec) := btOfList 9 ((([(5,[]),(1,[(1,3,5),(0,1,6),(1,19,2)]),(0,[(1,3,5),(0,1,6),(1,4,6)]),(6,[]),(1,[(0,4,5),(1,4,5),(3,43,18)]),(3,[(0,4,5),(1,4,5),(3,43,18)]),(4,[(0,4,5),(1,4,5),(3,43,18)]),(0,[(0,4,5),(1,4,5),(3,43,18)]),(0,[(0,4,5),(1,4,5),(3,0,18),(3,43,18)]),(4,[(0,4,5),(1,2,43),(1,4,5)]),(1,[(0,4,5),(1,2,43),(1,4,5)]),(3,[(0,4,5),(1,2,43),(1,4,5)]),(2,[(0,4,5),(1,2,43),(1,4,5)]),(0,[(0,4,5),(1,4,5),(1,3,18)]),(8,[]),(3,[(0,3,5),(1,1,11),(1,3,5)]),(0,[(0,3,5),(1,1,11),(1,3,5)]),(0,[(0,3,4),(1,3,4),(3,22,8)]),(4,[(2,4,5),(3,4,5),(1,38,39)]),(1,[(0,3,5),(1,1,11),(1,3,5)]),(3,[(0,3,4),(1,3,4),(3,22,8)]),(4,[(0,3,4),(1,3,4),(3,22,8)]),(1,[(0,3,4),(1,3,4),(3,22,8)]),(2,[(0,3,4),(1,3,4),(3,22,8)]),(0,[(0,4,5),(1,4,5),(3,43,18),(2,44,0)]),(1,[(2,4,5),(3,4,5),(1,38,39)]),(3,[(2,4,5),(3,4,5),(1,38,39)]),(2,[(2,4,5),(3,4,5),(1,38,39)]),(0,[(2,4,5),(3,4,5),(1,38,39)]),(2,[(0,4,5),(1,4,5),(3,43,18)]),(1,[(0,4,5),(1,43,3),(1,4,5)]),(0,[(1,3,4),(1,3,5),(0,8,5),(1,1,14)]),(0,[(0,4,5),(1,0,43),(1,4,5),(3,68,18)]),(4,[]),(2,[]),(1,[(3,4,5),(1,39,3)]),(3,[(2,3,5),(3,3,5)]),(1,[(2,3,5),(3,3,5)]),(2,[(2,3,5),(3,3,5)]),(4,[(2,3,5),(3,3,5)]),(0,[(2,3,5),(3,3,5)]),(3,[(1,3,5),(3,1,6)]),(2,[(1,3,5),(3,1,6)]),(2,[(1,3,5),(3,1,6),(1,45,4)]),(0,[(1,3,5),(3,1,6)]),(3,[]),(0,[]),(2,[(1,4,5),(0,0,18)]),(0,[(1,4,5),(0,0,18)]),(2,[(3,1,5),(1,107,1)]),(2,[(1,1,5)]),(0,[(3,0,5),(1,147,3),(3,1,150)]),(3,[(1,147,3),(3,1,150)]),(1,[(1,3,5),(3,1,6)]),(1,[(0,4,5),(1,4,5)]),(3,[(0,4,5),(1,4,5)]),(4,[(0,4,5),(1,4,5)]),(0,[(0,4,5),(1,4,5)]),(4,[(1,104,3)]),(2,[(3,1,5),(1,104,4)]),(4,[(1,3,4)]),(1,[(0,3,5),(1,3,5)]),(2,[(0,3,5),(1,3,5)]),(0,[(0,3,5),(1,3,5)]),(1,[(1,4,5),(3,0,18),(1,125,3)]),(0,[(3,1,3),(1,108,5),(3,1,5)]),(0,[(3,1,3),(3,1,5),(1,104,3)]),(0,[(1,4,3),(1,8,5),(3,1,9)]),(4,[(1,108,104)]),(3,[(0,3,5),(1,2,11)]),(4,[(1,108,5)]),(3,[(1,4,3)]),(4,[(1,104,4),(1,4,3)]),(7,[]),(3,[(1,4,3),(1,3,5)]),(4,[(1,4,3),(1,4,5)]),(4,[(1,4,5),(3,0,18)]),(1,[(0,4,5),(1,2,43)]),(3,[(0,4,5),(1,2,43)]),(4,[(0,4,5),(1,2,43)]),(4,[(1,4,3)]),(4,[(1,51,3)]),(2,[(1,51,3),(3,1,52)]),(4,[(1,4,5),(1,3,51)]),(1,[]),(4,[(2,3,4)]),(0,[(3,1,3),(3,1,5),(1,3,5)]),(2,[(1,1,5),(3,4,73)]),(1,[(1,3,5),(3,1,205)]),(1,[(0,4,5),(1,43,3)]),(3,[(0,4,5),(1,43,3)]),(4,[(0,4,5),(1,43,3)]),(0,[(0,4,5),(1,43,3)]),(3,[(1,97,3)]),(1,[(1,3,5),(3,4,5)]),(0,[(0,4,5),(3,43,5),(1,39,4)]),(0,[(0,3,4),(1,22,5),(1,3,4)]),(3,[(1,3,4)]),(3,[(0,3,5),(1,1,11)]),(2,[(1,4,5),(3,1,18)]),(0,[(3,4,5),(1,39,3),(3,1,42)]),(2,[(1,51,5),(3,4,223)]),(2,[(3,51,5),(1,107,1)]),(2,[(3,51,5),(1,107,4)]),(2,[(1,4,5)]),(3,[(0,3,4),(1,3,4)]),(4,[(0,3,4),(1,3,4)]),(0,[(0,3,4),(1,3,4)]),(3,[(1,55,4)]),(0,[(0,3,5),(1,3,5),(3,1,6)]),(0,[(1,1,3),(1,1,5),(1,3,5)]),(1,[(0,3,4),(1,3,4)]),(2,[(0,3,4),(1,3,4)]),(0,[(1,4,3),(1,4,5),(0,8,5)]),(0,[(1,4,3),(0,8,5),(1,1,14)]),(0,[(1,3,4),(0,8,5),(2,0,14)]),(0,[(0,4,5),(1,43,3),(1,4,5)]),(0,[(1,4,3),(0,8,5),(1,4,14)]),(0,[(1,3,4),(1,8,5),(0,0,9)]),(0,[(0,3,5),(1,1,11)]),(0,[(1,0,3),(1,55,5),(3,1,205)]),(3,[(2,3,5),(1,32,4)]),(0,[(1,3,5),(0,1,6),(3,19,6)]),(3,[(1,3,141),(3,1,205)]),(0,[(1,1,3),(1,173,5),(3,1,215)]),(2,[(1,51,5),(3,1,223)]),(3,[(3,1,3),(1,108,4)]),(1,[(1,3,5),(1,4,5)]),(3,[(0,3,5),(1,3,5)]),(0,[(3,4,5),(1,39,3)]),(1,[(3,4,5)]),(3,[(3,4,5)]),(2,[(3,4,5)]),(0,[(3,4,5)]),(2,[(3,4,5),(1,39,1)]),(4,[(1,3,5)]),(0,[(3,1,5),(1,3,5)]),(2,[(1,3,4)]),(3,[(1,4,141)]),(0,[(2,4,3),(3,115,5)]),(0,[(2,3,4),(1,210,5)]),(0,[(0,3,4),(3,22,5)]),(3,[(3,4,141)]),(0,[(1,0,5),(3,4,141)]),(0,[(1,0,4),(1,4,5)]),(3,[(1,4,5)]),(4,[(3,4,73)]),(3,[(1,3,141)]),(4,[(1,0,5)]),(1,[(1,0,5)]),(0,[(1,0,1),(1,164,5)]),(3,[(3,3,5)]),(0,[(3,3,5),(1,30,0)]),(3,[(3,1,5)]),(4,[(1,104,0)]),(0,[(3,1,5),(1,104,0)]),(0,[(1,0,3),(1,55,4)]),(3,[(3,1,141)]),(1,[(1,1,4)]),(0,[(1,1,4),(3,1,3)]),(1,[(1,3,5)]),(0,[(1,0,3),(1,55,5)]),(0,[(1,1,4),(1,4,3)]),(2,[(1,4,3)]),(0,[(3,1,3),(1,3,5)]),(4,[(3,0,5)]),(4,[(1,104,4)]),(0,[(1,1,4),(1,4,5)]),(0,[(1,1,4),(1,1,5)]),(0,[(3,0,4),(1,97,3)]),(4,[(3,4,5)]),(0,[(3,0,5),(1,147,3)]),(3,[(1,147,3)]),(3,[(1,1,5)]),(3,[(3,164,5)]),(4,[(3,164,5)]),(0,[(1,0,1),(3,164,5)]),(3,[(1,1,141)]),(0,[(1,1,5),(3,1,5)]),(0,[(0,4,5),(3,43,5)]),(0,[(1,1,5),(3,4,73)]),(0,[(3,4,5),(1,39,0)]),(3,[(3,140,5)]),(0,[(1,0,4),(3,140,5)]),(3,[(3,97,5)]),(0,[(3,0,4),(3,97,5)]),(0,[(1,0,5),(3,1,141)]),(0,[(1,0,5),(3,4,5)]),(1,[(1,4,5)]),(0,[(1,0,5),(1,4,5)]),(3,[(1,1,3)]),(4,[(1,4,5)]),(2,[(1,1,3)]),(0,[(1,3,4),(1,8,5)]),(1,[(1,3,4),(1,8,5)]),(2,[(1,3,4),(1,8,5)]),(0,[(3,1,3),(3,1,5)]),(0,[(3,1,5),(1,104,3)]),(3,[(1,3,5)]),(0,[(0,3,4),(1,22,5)]),(0,[(1,1,4),(3,51,5)]),(0,[(1,1,3),(1,173,5)]),(0,[(1,4,3),(3,1,8)]),(1,[(1,3,4)]),(0,[(1,3,4),(2,3,5)]),(0,[(3,1,3),(1,108,5)]),(0,[(1,4,3),(1,4,5)]),(1,[(1,4,3),(1,4,5)]),(0,[(1,3,4),(0,8,5)]),(2,[(3,1,5)]),(0,[(1,3,4)]),(0,[(1,4,5),(3,1,18)]),(0,[(1,3,4),(2,8,5)]),(1,[(1,3,4),(2,8,5)]),(2,[(1,3,4),(2,8,5)]),(0,[(1,4,5),(3,4,5)]),(0,[(1,3,4),(3,8,5)]),(0,[(2,3,4),(3,3,4)]),(0,[(2,3,4),(1,3,5)]),(3,[(0,3,5),(1,11,4)]),(0,[(0,3,5),(1,11,4)]),(0,[(1,1,0),(1,1,5)]),(3,[(0,4,5),(3,43,3)]),(0,[(0,4,5),(3,43,3)]),(2,[(1,3,5)]),(0,[(1,3,5)]),(1,[(0,4,5)]),(3,[(0,4,5)]),(3,[(0,3,5)]),(4,[(0,4,5)]),(2,[(0,3,5)]),(4,[(0,3,5)]),(0,[(0,4,5)]),(0,[(0,3,5)]),(0,[(1,4,5)]),(0,[(2,3,4),(1,210,4)]),(3,[(2,3,5)]),(2,[(2,3,5)]),(4,[(2,3,5)]),(0,[(2,3,5)]),(0,[(1,1,3),(1,1,5)]),(0,[(2,4,5),(1,38,3)]),(0,[(3,0,5),(3,4,5)]),(0,[(1,3,5),(3,4,6)]),(1,[(1,3,5),(3,4,6)]),(0,[(2,3,5),(1,32,5)]),(3,[(2,3,4)]),(0,[(2,3,4)]),(0,[(3,1,5)]),(3,[(0,3,4)]),(0,[(0,3,4)]),(0,[(1,0,5)]),(3,[(3,1,3)]),(0,[(3,1,3)]),(0,[(1,1,3)]),(0,[(1,0,3)]),(0,[(1,0,1)])] : List PoolSpec)).map some)
def B_34_2 : BT (List (List Nat)) := BT.empty
lemma B_34_2_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 2 xs.toFinset) B_34_2 := .empty
def P_34_3 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 r_34 S_34 ps_34 []
def N_34_3 : List NodeSpec := [([10,0,1,12],[],[]),([10,0,2,13],[],[]),([3,16,17,18],[],[]),([0,4,21,6],[],[]),([23,0,1,15],[],[]),([0,1,2,27],[],[]),([0,1,15,26],[],[]),([0,1,28,26],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_3 : checkNodesBT W_34 g_34 F_34 P_34_3 A_34 B_34_2 3 N_34_3 = true := by decide +kernel
def B_34_3 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_3
set_option maxRecDepth 500000 in
lemma B_34_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 3 xs.toFinset) B_34_3 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound S_34_ok) A_34_ok B_34_2_ok C_34_3
def P_34_4 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 r_34 S_34 ps_34 []
def N_34_4 : List NodeSpec := [([29,0,1,2,31],[],[]),([32,0,1,2,35],[],[]),([32,0,1,36,34],[],[]),([32,37,1,2,34],[],[]),([41,0,1,2,42],[],[]),([44,45,0,2,3],[],[]),([46,0,1,2,48],[],[]),([49,0,1,2,50],[],[]),([44,54,0,2,3],[],[]),([44,58,1,2,3],[],[]),([60,0,1,2,61],[],[0]),([44,63,0,1,3],[],[]),([44,64,1,2,3],[],[]),([65,0,1,2,62],[],[0]),([32,0,1,34,66],[],[]),([44,0,1,3,12],[],[]),([67,0,1,3,18],[],[]),([54,0,12,4,6],[],[]),([0,1,50,66,9],[],[1]),([32,1,2,34,68],[],[]),([44,0,2,3,13],[],[]),([0,2,13,69,18],[],[]),([45,2,3,68,18],[],[]),([45,0,3,66,18],[],[]),([2,3,13,68,18],[],[]),([70,71,1,2,68],[],[1]),([72,1,3,15,18],[],[1]),([0,4,74,15,6],[],[]),([0,20,4,14,6],[],[0]),([0,2,74,6,18],[],[]),([29,1,2,4,75],[],[]),([46,0,20,8,5],[],[]),([0,2,4,74,6],[],[]),([76,0,1,2,22],[],[]),([32,0,1,15,18],[],[]),([10,0,1,2,11],[],[0]),([0,1,22,15,9],[],[0]),([0,2,77,74,6],[],[]),([79,80,3,4,5],[],[]),([24,0,1,15,5],[],[0]),([81,1,3,15,18],[],[]),([44,82,0,2,3],[],[]),([83,1,4,15,6],[],[]),([85,0,1,2,86],[],[0]),([87,0,2,4,6],[],[]),([81,2,4,74,6],[],[]),([88,0,1,2,90],[],[]),([0,1,3,92,18],[],[]),([54,93,3,4,5],[],[]),([32,94,0,1,2],[],[]),([0,2,4,96,6],[],[]),([0,2,100,4,6],[],[]),([0,1,3,101,18],[],[]),([70,71,0,1,66],[],[1]),([0,2,4,102,6],[],[0]),([103,1,2,3,18],[],[]),([0,1,12,69,18],[],[]),([0,1,106,4,6],[],[]),([44,109,0,2,3],[],[]),([44,78,0,1,3],[],[]),([0,1,8,15,84],[],[]),([81,1,4,15,6],[],[]),([24,0,2,74,5],[],[]),([0,1,3,15,18],[],[]),([25,0,1,2,26],[],[0]),([0,3,74,15,18],[],[]),([0,3,13,66,18],[],[]),([24,78,0,1,5],[],[]),([24,54,0,2,5],[],[]),([110,0,3,4,5],[],[]),([0,1,3,113,18],[],[]),([24,0,1,28,5],[],[0]),([54,0,3,66,18],[],[]),([23,0,1,2,14],[],[0]),([32,1,2,75,18],[],[]),([0,13,4,66,6],[],[]),([24,0,114,2,5],[],[]),([45,0,4,15,6],[],[]),([0,2,8,74,84],[],[]),([117,0,3,4,5],[],[]),([0,1,15,6,18],[],[]),([2,3,75,74,18],[],[]),([0,2,69,74,18],[],[]),([54,2,3,68,18],[],[]),([0,1,2,14,26],[],[0]),([0,4,15,17,6],[],[1]),([83,1,3,15,18],[],[]),([0,2,118,4,6],[],[]),([0,2,51,119,6],[],[]),([0,3,15,17,18],[],[0]),([44,0,1,120,3],[],[]),([0,1,3,121,18],[],[]),([0,1,69,15,18],[],[]),([44,0,122,2,3],[],[]),([29,0,1,4,15],[],[]),([0,1,3,34,15],[],[]),([3,4,16,17,5],[],[0,1]),([0,2,13,7,9],[],[0]),([78,0,13,4,6],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_4 : checkNodesBT W_34 g_34 F_34 P_34_4 A_34 B_34_3 4 N_34_4 = true := by decide +kernel
def B_34_4 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_4
set_option maxRecDepth 500000 in
lemma B_34_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 4 xs.toFinset) B_34_4 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound S_34_ok) A_34_ok B_34_3_ok C_34_4
def P_34_5 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 r_34 S_34 ps_34 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
def N_34_5_0 : List NodeSpec := [([0,1,120,42,4,5],[],[1]),([0,122,2,42,4,5],[],[1]),([32,123,1,2,4,5],[],[]),([32,89,0,1,2,31],[],[0]),([32,30,123,1,2,4],[],[1]),([32,33,0,1,2,34],[],[0,1]),([32,30,0,1,36,4],[],[0,1]),([124,39,44,1,2,3],[],[]),([10,0,1,2,3,5],[],[0]),([127,0,2,3,4,5],[],[]),([32,30,125,1,2,4],[],[1]),([45,125,2,3,4,5],[],[]),([78,72,1,3,4,5],[],[1]),([46,0,20,3,4,5],[0],[0]),([0,20,3,4,5,9],[1,2],[0,1]),([39,1,93,3,5,18],[3],[]),([32,0,1,2,43,34],[],[0]),([45,0,2,3,43,18],[],[0]),([39,59,0,1,2,4],[],[]),([0,129,3,42,4,5],[],[]),([44,0,1,2,11,3],[4,5,6,7],[0]),([0,1,2,48,4,6],[0],[0]),([54,0,2,11,4,6],[],[0,1]),([54,0,2,3,43,18],[],[0]),([0,1,2,11,7,9],[],[0,1]),([46,59,0,1,2,4],[],[]),([44,0,1,2,50,3],[],[]),([124,44,1,2,3,18],[3],[]),([127,125,2,3,4,5],[],[]),([44,0,1,2,130,3],[4,5],[1]),([60,59,0,1,2,4],[],[0]),([44,0,1,2,3,62],[4,6,7],[0]),([65,44,0,1,2,3],[],[0]),([44,125,1,2,3,18],[3],[]),([44,125,1,2,3],[3,8],[]),([45,0,2,77,5,6],[],[]),([0,1,3,34,66,5],[3],[0]),([0,1,2,131,4,5],[],[1]),([32,30,0,1,4,66],[],[0,1]),([44,0,1,2,3,6],[6],[0]),([32,0,1,3,66,18],[],[]),([0,1,3,66,6,18],[9],[0]),([0,1,11,3,66,18],[9,10,11],[0]),([45,0,12,4,5,6],[],[]),([39,0,1,12,4,6],[],[]),([46,0,1,12,4,6],[],[1]),([0,1,3,66,18,9],[10,12,13],[0,1]),([45,0,12,4,6],[14],[]),([32,30,1,2,4,68],[],[0,1]),([45,2,3,4,68,5],[],[0]),([0,2,3,13,43,18],[],[0]),([2,3,13,4,68,5],[],[0,1]),([32,1,2,3,68,18],[],[]),([0,2,13,4,6,18],[15],[1]),([0,2,13,43,4,6],[15,16],[0,1]),([0,1,2,42,77,5],[],[]),([124,1,2,3,5,18],[],[]),([46,0,2,13,4,6],[],[1]),([70,1,2,3,68,18],[3],[0,1]),([44,0,1,2,132,3],[],[]),([0,2,13,7,4,6],[],[0]),([116,0,2,3,4,5],[],[0]),([24,0,1,2,14,5],[0,17],[0,1]),([133,0,1,3,4,5],[],[]),([0,1,2,8,5,26],[0],[0]),([24,0,1,2,86,5],[],[0]),([134,0,1,3,4,5],[],[]),([0,1,2,14,8,84],[],[0,1]),([81,1,2,3,14,18],[],[0,1]),([44,0,1,2,3,42],[18],[0]),([70,0,1,3,66,18],[10,11],[0]),([104,0,2,3,4,136],[],[]),([0,1,2,3,91,18],[],[0,1]),([54,58,2,3,4,5],[],[]),([0,1,106,3,4,5],[],[0]),([135,0,2,3,137,5],[],[]),([39,0,2,13,4,6],[],[]),([139,0,1,3,4,5],[],[]),([0,2,3,14,74,18],[],[0,1]),([145,0,2,3,4,5],[],[]),([0,1,3,121,4,5],[],[0,1]),([0,1,2,3,146,18],[],[1]),([70,71,0,1,2,43],[],[0,1]),([32,0,1,2,14,18],[],[0]),([0,149,2,3,4,5],[],[]),([45,58,2,3,4,5],[],[]),([151,2,3,4,5,141],[],[]),([32,0,2,4,74,5],[],[0]),([108,0,2,153,4,5],[],[]),([108,154,2,3,4,5],[],[]),([0,2,13,4,69,5],[0],[0]),([157,0,2,3,4,5],[],[]),([0,1,3,15,18],[],[0,1]),([0,1,2,158,8,5],[],[]),([0,2,3,4,74,5],[],[0]),([0,1,50,3,66,18],[],[0]),([0,2,3,4,96,5],[],[0]),([0,2,4,52,73,6],[3],[0]),([0,2,13,4,6,9],[0,16,19],[0,1]),([0,1,2,22,14,9],[],[0]),([70,44,0,1,2,3],[4,5],[]),([45,0,159,2,4,5],[],[]),([109,0,2,3,4,5],[],[]),([0,1,3,4,15,5],[],[0,1]),([0,2,51,8,73,6],[3],[0]),([32,0,1,4,15,5],[],[0,1]),([160,78,1,3,4,5],[],[]),([124,125,1,2,3,18],[3],[]),([88,0,1,2,8,84],[],[]),([54,0,2,3,4,5],[],[]),([39,1,2,3,143,141],[3],[]),([0,2,3,100,4,5],[],[0]),([0,1,2,3,112,18],[],[0,1]),([0,1,3,66,77,5],[3],[1]),([162,0,2,3,4,5],[],[]),([0,1,2,3,95,18],[],[0,1]),([108,0,2,163,4,5],[],[]),([166,167,2,3,4,5],[],[]),([0,1,2,3,34,14],[],[0]),([135,104,0,2,4,6],[],[]),([0,1,2,3,99,18],[],[0,1]),([78,0,1,3,4,5],[],[]),([25,24,0,1,2,5],[17,20,21],[0,1]),([24,0,1,2,5,26],[],[0]),([168,0,2,3,4,5],[],[]),([0,2,42,13,4,5],[0],[1]),([142,1,2,3,141,18],[3],[]),([44,125,1,2,3,5],[],[]),([169,125,1,2,3,5],[],[]),([78,0,1,11,4,6],[],[0,1]),([0,2,3,77,74,5],[],[0]),([0,170,2,3,51,5],[],[]),([0,3,4,15,17,5],[],[0]),([32,30,37,1,2,4],[],[0,1]),([171,172,2,3,4,5],[],[]),([177,0,1,3,4,5],[],[]),([32,0,1,2,69,18],[],[]),([0,2,3,51,119,5],[],[0]),([179,0,2,3,4,5],[],[]),([0,180,2,175,4,5],[],[]),([0,1,3,77,15,5],[],[0,1]),([104,0,159,2,4,6],[0],[]),([0,2,3,4,91,73],[3],[]),([181,1,2,3,143,5],[],[]),([0,3,13,4,66,5],[],[0]),([182,0,2,3,4,5],[],[]),([24,0,1,2,5,9],[17,22,23],[0,1]),([124,44,1,2,3,5],[24],[]),([0,1,2,69,77,5],[],[]),([89,24,0,1,2,5],[],[]),([32,44,0,1,2,3],[],[]),([0,2,22,8,74,5],[],[0]),([0,1,22,8,15,5],[],[0]),([40,44,0,1,2,3],[25,26,27,28],[0]),([78,0,1,22,8,5],[],[0]),([44,0,1,2,3,9],[4,7,29],[0]),([39,0,1,3,4,15],[],[0,1]),([23,0,1,2,8,5],[0],[0]),([184,0,2,3,4,5],[],[]),([0,1,3,8,15,18],[],[]),([0,1,11,4,66,6],[],[0,1]),([89,0,1,3,4,15],[],[0,1]),([185,0,2,3,4,5],[],[0]),([88,89,0,1,2,22],[],[0]),([133,125,1,3,4,5],[],[]),([79,78,0,3,4,5],[],[0]),([0,1,2,90,8,5],[0],[0]),([32,1,2,4,75,5],[],[0]),([0,1,3,4,101,5],[],[0,1]),([0,20,4,8,5,6],[3],[0]),([72,1,2,3,14,18],[],[0,1]),([0,1,2,11,69,18],[30],[0]),([45,0,2,7,8,5],[],[]),([0,3,4,74,15,5],[],[0]),([45,0,2,4,69,5],[],[]),([41,39,0,1,2,3],[3],[0]),([0,1,2,14,6,18],[],[0,1]),([29,30,0,1,2,4],[0],[0]),([0,2,4,74,6],[31],[0]),([105,0,1,2,4,6],[],[0]),([152,0,2,3,111,5],[],[]),([83,1,3,4,15,5],[],[0]),([109,0,2,3,5,18],[],[]),([0,2,4,14,74,6],[31],[0,1]),([81,1,2,4,14,6],[],[0]),([124,1,2,3,18],[3,32],[]),([85,0,1,2,8,5],[],[]),([0,1,3,14,15,18],[],[0,1]),([0,1,2,14,69,18],[],[0,1]),([186,0,2,3,4,5],[],[]),([85,24,0,1,2,5],[],[0]),([29,0,1,2,4,14],[],[0,1]),([29,0,1,2,4,6],[],[0]),([45,0,3,4,66,5],[],[0]),([46,0,19,2,8,5],[],[0]),([0,2,4,8,74,6],[],[]),([0,2,4,74,5,6],[],[0,1]),([54,72,2,3,4,5],[],[0]),([0,1,2,3,75,18],[],[]),([0,2,3,74,5,18],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_5_0 : checkNodesBT W_34 g_34 F_34 P_34_5 A_34 B_34_4 5 N_34_5_0 = true := by decide +kernel
def N_34_5_1 : List NodeSpec := [([0,1,3,15,5,18],[],[0]),([29,0,1,2,4,5],[],[1]),([0,1,2,3,14,18],[],[0,1]),([54,0,2,22,8,5],[],[0]),([88,46,0,1,2,3],[],[]),([0,2,3,4,74,6],[],[]),([0,1,3,4,15,6],[],[]),([39,1,2,3,4,75],[],[1]),([32,38,89,0,1,2],[],[0,1]),([135,0,2,175,4,5],[],[]),([2,3,4,75,74,5],[],[0,1]),([81,2,3,4,74,5],[],[0]),([0,2,4,69,74,5],[],[0]),([45,0,2,4,14,6],[],[0]),([104,0,180,2,4,6],[0],[]),([88,24,0,1,2,5],[],[]),([81,1,3,4,15,5],[],[0]),([0,1,3,4,15,9],[],[0]),([76,0,1,2,3,4],[],[0]),([78,45,0,3,4,5],[],[]),([54,187,2,3,4,5],[],[]),([89,44,0,1,2,3],[],[]),([78,187,1,3,4,5],[],[]),([49,0,1,2,3,18],[3],[0]),([124,44,1,2,3],[5,24],[]),([0,1,2,42,34,5],[],[]),([78,54,0,3,4,5],[],[]),([46,71,0,1,2,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_5_1 : checkNodesBT W_34 g_34 F_34 P_34_5 A_34 B_34_4 5 N_34_5_1 = true := by decide +kernel
def N_34_5 := N_34_5_0 ++ N_34_5_1
def B_34_5 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_5
set_option maxRecDepth 500000 in
lemma B_34_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 5 xs.toFinset) B_34_5 := by
  have hP := buildPoolsSubBT_sound (pdepth := 9) (W := W_34) (raw := r_34) (pspecs := ps_34) (used := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]) S_34_ok
  have hm0 := checkNodesBT_mem (by decide) gp_34 W_34_ok hP A_34_ok B_34_4_ok C_34_5_0
  have hm1 := checkNodesBT_mem (by decide) gp_34 W_34_ok hP A_34_ok B_34_4_ok C_34_5_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def P_34_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 r_34 S_34 ps_34 [0,3,7,9,11,14,15,16,17,20,26,28,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128]
def N_34_6_0 : List NodeSpec := [([39,109,0,2,3,4,5],[],[0,1]),([109,0,2,3,42,4,5],[33],[]),([188,1,2,3,4,34,5],[],[1]),([189,0,1,2,3,4,5],[34],[]),([40,0,1,2,42,4,5],[35],[0,1]),([0,190,1,2,4,5,6],[],[]),([191,0,1,2,3,4,5],[],[]),([32,39,30,0,1,2,4],[],[0]),([32,38,39,0,1,2,3],[],[0]),([39,44,0,1,2,3,5],[3],[]),([32,89,30,0,1,2,4],[],[0,1]),([32,30,0,1,2,4,34],[36],[0,1]),([39,44,0,1,2,3],[3,26,28],[0]),([32,0,1,2,192,4,5],[0],[]),([70,71,0,1,2,4,5],[],[0,1]),([54,0,2,3,4,5,6],[0],[0]),([0,1,2,50,4,5,9],[],[1]),([46,0,1,2,3,5,18],[3],[0]),([0,1,2,3,42,5,18],[],[0]),([0,193,1,2,3,5,18],[3],[1]),([46,45,0,2,3,4,5],[],[]),([70,125,1,2,3,4,5],[],[1]),([45,0,2,3,7,4,5],[],[0]),([39,125,1,2,3,5,18],[3],[]),([32,33,30,0,1,2,4],[37,38,39,40],[0,1]),([142,125,1,2,3,5,18],[3],[]),([32,125,1,2,3,4,5],[],[0]),([45,0,2,3,4,5,18],[41],[0]),([39,125,1,2,3,4,5],[3],[]),([194,45,0,2,3,4,5],[42],[]),([109,0,1,2,3,4,5],[],[]),([45,0,2,3,4,195,5],[41,43,44],[1]),([196,45,0,2,3,4,5],[41],[]),([45,0,197,2,3,4,5],[41],[]),([39,72,1,2,3,5,18],[3],[0]),([105,0,1,2,3,4,5],[0,34,45,46],[0,1]),([72,1,2,3,4,5,9],[47,48],[0,1]),([104,0,198,2,3,4,5],[33,46,49],[]),([32,0,1,2,8,5,18],[0],[0]),([151,0,2,3,150,4,5],[33],[]),([0,1,2,3,4,5,138],[33,46],[0,1]),([0,2,3,4,137,5,73],[50],[]),([151,0,2,3,4,5],[51,52],[0,1]),([32,0,1,2,4,34,5],[0],[0]),([0,2,3,4,51,5,199],[3],[]),([45,0,2,3,4,51,5],[34],[]),([45,0,2,3,4,5,9],[34,44,53],[0]),([0,1,2,50,8,5,18],[0],[1]),([200,0,1,2,3,4,5],[],[]),([0,1,2,11,3,43,18],[54,55,56,57],[0,1]),([45,0,2,3,175,4,5],[58],[]),([39,0,1,2,3,137,5],[3,59],[]),([45,0,2,3,4,5,73],[0,33],[1]),([0,1,2,3,42,4,5],[33],[0]),([39,0,1,120,3,4,5],[0],[0,1]),([39,0,1,2,3,141,18],[3],[0]),([104,0,1,2,4,8,6],[60],[0]),([45,0,2,3,4,5,141],[41],[]),([0,1,2,11,4,6,9],[61,62,63],[0,1]),([169,0,1,2,3,141,18],[3],[0]),([201,0,1,2,3,4,5],[34],[]),([202,0,1,2,3,4,5],[],[]),([142,39,1,2,3,4,141],[3,45],[0]),([107,0,1,2,3,5,18],[3],[]),([39,147,1,2,3,4,141],[3,45],[0]),([89,0,1,2,3,4,14],[46],[0,1]),([0,1,2,3,126,4,5],[33,46,64],[0,1]),([104,0,2,3,4,73,6],[0],[1]),([0,1,2,3,183,4,5],[33],[0]),([203,0,1,2,3,4,5],[],[]),([204,0,1,2,3,4,5],[],[0]),([89,0,1,2,132,4,5],[],[0,1]),([0,2,3,175,4,5,73],[0],[1]),([104,0,2,3,4,199],[0,65],[]),([45,0,2,3,4,5,205],[0],[]),([194,0,1,2,3,4,5],[],[]),([142,0,1,2,3,5,18],[3],[0]),([0,206,1,2,3,5,18],[3],[1]),([171,0,2,3,4,5,207],[0,46],[0]),([0,1,2,3,209,4,5],[33],[0]),([108,0,2,175,4,5],[0,66],[1]),([108,104,0,2,4,5,6],[0],[]),([72,1,2,3,8,5,18],[0],[0,1]),([54,0,2,3,4,5],[67],[]),([104,45,0,2,3,4,5],[68],[]),([169,0,1,2,3,8,5],[0],[]),([171,0,2,3,4,5,73],[33],[0]),([0,1,3,12,4,5,18],[69],[1]),([0,155,1,2,3,5,18],[3],[]),([0,1,2,3,156,4,5],[33],[0]),([45,0,2,3,4,5,199],[70],[]),([0,1,2,3,137,8,5],[0,71,72],[0]),([0,1,3,66,5,18],[3,9,73],[0,1]),([89,0,1,2,3,4,5],[],[]),([0,1,2,3,4,211,18],[0,3],[]),([212,0,1,2,3,4,5],[],[]),([213,0,1,2,3,4,5],[0,33],[0]),([151,147,0,2,3,4,5],[52],[0]),([0,198,2,3,173,4,5],[0],[]),([78,0,1,3,4,5,6],[],[0,1]),([0,1,2,8,5,6,18],[0,3,74,75],[0]),([0,1,2,3,4,95,5],[0,3,33,46],[0,1]),([0,1,2,3,14,5,18],[3],[0,1]),([108,125,1,2,3,4,5],[76],[]),([0,1,2,3,178,4,5],[33],[0]),([107,0,2,3,4,5,73],[3],[]),([142,147,0,1,2,3,18],[3],[0,1]),([0,1,11,3,4,66,5],[3,73,77,78,79],[0]),([135,0,2,3,51,8,5],[80],[]),([104,0,2,3,4,5,199],[0],[]),([46,0,1,2,55,4,5],[45],[]),([54,0,2,3,4,5,9],[34,67],[0]),([135,0,2,3,4,52,5],[3,81,82],[]),([45,0,2,3,4,73,6],[0,33],[1]),([0,1,2,3,52,5,18],[0,83],[0]),([0,1,2,3,4,176,5],[46,84],[0,1]),([210,45,0,2,4,5,6],[53,85],[]),([214,0,1,2,3,4,5],[],[]),([108,104,0,2,4,6],[0,86],[0]),([45,0,2,173,4,5,6],[0],[]),([0,180,2,3,4,51,5],[34],[]),([216,0,1,2,3,4,5],[],[]),([208,0,1,2,3,5,18],[3,87],[]),([45,0,2,55,4,5,6],[0,53],[]),([39,1,2,3,55,4,141],[0],[]),([0,1,2,3,143,8,5],[0],[1]),([0,1,2,3,51,5,9],[34],[]),([0,2,3,4,52,5,73],[0],[0]),([0,1,2,3,99,4,5],[0,3,33,45,46],[0,1]),([152,0,2,3,51,5,18],[34],[]),([0,1,2,3,217,5,18],[0,3],[]),([218,0,2,3,4,5,6],[0,33,88],[]),([88,0,1,2,3,51,5],[33],[]),([39,147,0,1,2,3,143],[3],[0]),([45,0,2,3,4,5,215],[0,46],[1]),([0,1,2,11,4,69,5],[0,3,89,90,91,92],[0,1]),([0,1,2,3,98,5,18],[93],[0]),([39,0,1,2,11,4,6],[94],[0]),([219,0,1,2,3,4,5],[],[]),([107,108,0,2,3,4,5],[],[0]),([45,0,220,2,3,4,5],[42],[]),([108,0,2,3,4,137,5],[],[0]),([169,0,1,2,3,5,18],[3],[0]),([164,2,3,4,5,141,73],[0],[]),([0,1,2,3,34,140,5],[45],[]),([0,1,2,3,221,5,18],[3],[]),([0,222,1,2,3,4,5],[],[]),([0,1,2,3,8,5,223],[0,71],[]),([0,2,3,4,51,73,6],[0,3],[0]),([78,0,1,3,4,8,5],[],[0]),([0,2,3,51,8,5,73],[0],[0]),([39,0,1,2,3,5,18],[3,95],[]),([171,164,2,3,4,5,141],[33],[]),([54,0,2,3,4,5,18],[],[0,1]),([208,0,2,3,51,5,73],[34],[]),([165,0,167,2,3,4,5],[0,46],[0]),([142,0,1,2,3,143,5],[3,46],[1]),([39,0,1,2,3,34,5],[3,46],[0]),([108,0,2,4,51,5,6],[3],[]),([32,71,0,1,2,4,5],[0],[]),([0,1,2,3,163,4,5],[],[0]),([0,1,2,8,5,84],[0,96],[0]),([0,1,2,55,8,5,18],[0,97],[1]),([88,0,1,2,3,4,9],[46],[0,1]),([0,2,3,13,4,5,18],[98],[0,1]),([104,0,180,2,3,4,5],[33,46],[0]),([0,1,2,3,4,146,5],[3],[0,1]),([169,1,2,3,140,5,141],[3,45],[]),([224,0,1,2,3,4,5],[],[]),([152,0,2,3,4,5,73],[33,99],[]),([109,0,2,3,4,5],[100],[0,1]),([142,193,1,2,3,4,5],[3,46],[1]),([218,0,2,3,4,5,205],[33],[]),([108,45,0,2,4,5,6],[0],[0]),([208,0,1,2,3,5,223],[3,46,101],[]),([104,0,167,2,3,4,5],[33,46],[0]),([107,0,198,2,3,4,5],[3,46,102],[]),([0,226,1,2,3,4,5],[45],[]),([0,1,2,3,227,4,5],[],[0]),([0,2,173,4,5,73,6],[0],[1]),([0,1,2,3,161,4,5],[33],[0]),([107,0,1,2,3,137,5],[3,103],[]),([169,0,1,2,3,5,228],[3,46],[0]),([108,104,0,2,175,4,5],[58],[]),([0,166,2,3,4,5,73],[],[]),([108,0,2,3,51,5,18],[3,104],[0]),([0,1,2,22,14,8,5],[0,105,106,107],[0,1]),([39,0,2,3,13,4,5],[0],[0,1]),([229,0,1,2,3,4,5],[],[]),([165,0,2,3,4,5,73],[0],[]),([0,1,2,3,34,51,5],[34],[]),([135,0,1,2,3,5,18],[75,104],[]),([0,1,2,3,56,5,18],[0,108],[0,1]),([230,0,1,2,3,4,5],[],[]),([45,0,2,3,4,140,5],[41],[]),([45,0,2,11,4,6],[0,109],[0,1]),([135,104,0,2,3,4,5],[],[0]),([0,20,3,4,5,6],[0,3,14],[0,1]),([0,1,2,3,4,5,136],[],[0]),([39,147,0,1,2,3,18],[3],[1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_6_0 : checkNodesBT W_34 g_34 F_34 P_34_6 A_34 B_34_5 6 N_34_6_0 = true := by decide +kernel
def N_34_6_1 : List NodeSpec := [([0,2,13,4,5,6],[0,15,16],[0,1]),([0,1,2,3,8,141,18],[97],[0,1]),([0,2,173,4,73,6],[0,110],[0,1]),([89,0,1,2,3,5,18],[0],[0]),([104,125,1,2,3,4,5],[76],[]),([24,0,1,2,5],[0,17,20],[0]),([0,1,2,11,42,4,5],[0,35],[0,1]),([0,1,2,22,8,5,9],[107,111,112],[0,1]),([231,0,1,2,3,4,5],[34],[]),([0,232,1,2,3,4,5],[],[]),([88,0,1,2,22,8,5],[0],[0]),([24,0,1,2,8,5],[0,17,20],[0]),([89,0,1,2,22,8,5],[],[0]),([0,1,2,3,77,5,18],[0],[0,1]),([108,152,0,2,3,4,5],[],[0]),([152,0,1,2,3,8,5],[0,75],[]),([0,1,2,3,14,18],[113],[0,1]),([142,1,2,3,4,5,141],[3],[0]),([0,1,2,3,14,8,18],[],[0,1]),([54,0,2,3,4,8,5],[],[0]),([88,0,1,2,3,8,18],[],[0]),([46,0,1,2,3,8,5],[0],[0]),([0,1,2,3,4,14,6],[0],[0]),([88,0,1,2,3,4,6],[0],[0]),([0,233,1,2,3,4,5],[],[1]),([0,1,2,3,8,5,18],[0,71],[0]),([45,0,2,4,8,5,6],[60],[0]),([0,1,2,3,4,5,9],[34,46,84],[0,1]),([0,1,2,3,234,8,5],[0,3,71],[]),([0,235,1,2,3,4,5],[],[]),([39,0,1,2,3,77,5],[0,3],[0]),([108,0,1,2,42,4,5],[33],[]),([32,38,0,1,2,8,5],[0],[0]),([32,0,1,2,4,14,5],[0,3],[0,1]),([78,0,1,3,4,5,9],[46],[0,1]),([0,1,2,3,4,5,57],[34,46],[0,1]),([39,0,1,2,3,4,211],[3],[]),([44,0,1,2,3],[3,7],[0,1]),([0,1,2,3,153,4,5],[],[0]),([32,89,0,1,2,4,5],[],[0]),([0,1,2,3,217,4,6],[0],[]),([45,0,2,3,43,4,5],[0,44],[0]),([39,0,1,2,3,4,14],[3,46],[0,1]),([46,0,19,2,3,4,5],[0],[0]),([88,39,0,1,2,3,4],[3],[]),([0,1,2,3,4,75,5],[],[0]),([0,2,3,4,14,74,5],[33,114],[0,1]),([81,1,2,3,4,14,5],[0,3,115],[0,1]),([39,147,193,1,2,3,4],[45],[1]),([0,1,3,4,8,15,5],[],[0,1]),([0,1,3,4,15,5],[],[0,1]),([0,1,2,69,5,18],[3,116],[0,1]),([135,0,1,2,4,5,6],[80],[0]),([0,1,3,4,14,15,5],[46],[0,1]),([0,1,2,3,14,77,5],[0,117],[0,1]),([39,0,122,2,3,4,5],[0],[0,1]),([45,0,2,3,4,8,5],[0],[]),([78,0,1,3,4,5],[],[0,1]),([104,45,0,2,3,4,6],[0],[]),([236,0,1,2,3,4,5],[],[]),([0,2,3,4,8,74,5],[],[0]),([39,45,0,2,3,4,5],[],[1]),([88,0,1,2,3,4,5],[],[]),([0,1,2,3,4,14,9],[],[0]),([187,1,2,3,4,5,9],[0,118],[0,1]),([54,0,1,2,3,4,5],[],[]),([0,1,2,3,34,8,5],[0,97],[0]),([46,0,1,2,3,4,5],[],[]),([46,0,1,2,3,5,9],[46],[0]),([0,1,2,3,4,14,5],[0,3,33,45,46],[0,1]),([88,89,0,1,2,3,4],[],[0]),([0,237,1,2,3,4,5],[84],[]),([89,0,1,2,3,34,5],[46],[0]),([46,0,1,2,8,5,6],[3],[0]),([39,0,1,2,3,4,238],[0,3],[]),([210,125,1,2,3,4,5],[3],[1]),([210,71,0,1,2,4,5],[0],[]),([32,30,0,1,2,43,4],[0,38,40],[0,1]),([239,0,1,2,3,4,5],[45],[]),([0,2,13,4,6],[0,15,16],[0,1]),([0,2,3,13,43,4,5],[0,98,119],[0]),([218,0,2,3,4,5],[120],[]),([210,0,1,2,42,4,5],[0,35,85],[]),([32,1,2,3,4,68,5],[],[0]),([32,30,0,1,2,4,18],[36],[0,1]),([0,1,2,3,240,5,18],[0,3,121],[]),([0,1,3,66,18],[3,11,73],[0,1]),([0,1,2,11,7,4,6],[],[0,1]),([32,0,1,3,4,66,5],[],[0]),([32,0,1,2,4,69,5],[],[0]),([45,0,2,3,4,5,6],[0,122],[]),([39,0,1,2,3,143,5],[3,46],[0,1]),([89,0,1,2,3,77,5],[],[0]),([218,0,2,3,4,5,141],[123],[]),([39,0,1,3,12,4,5],[0],[0,1]),([0,1,2,3,69,5,18],[],[0]),([45,0,2,3,4,5],[124],[]),([44,0,1,2,3,18],[3,7],[0,1]),([0,2,3,4,74,5],[114],[0,1]),([70,0,1,2,3,43,18],[54,55],[0,1]),([142,125,1,2,3,4,5],[3],[]),([46,0,1,2,11,4,6],[],[0,1]),([32,30,0,1,2,31,4],[],[0,1]),([152,0,2,3,4,5,223],[3,46,125],[]),([44,0,1,2,3,5,18],[3,7],[0]),([0,1,2,3,111,5,18],[0,126],[0]),([45,0,2,11,4,5,6],[53],[0,1]),([44,0,1,2,3,5],[3,7],[0,1]),([0,1,2,11,4,6,18],[127,128],[0,1]),([32,0,1,2,3,43,18],[],[0]),([0,1,2,3,241,4,5],[0],[]),([45,242,0,2,3,4,5],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_6_1 : checkNodesBT W_34 g_34 F_34 P_34_6 A_34 B_34_5 6 N_34_6_1 = true := by decide +kernel
def N_34_6 := N_34_6_0 ++ N_34_6_1
def B_34_6 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_6
set_option maxRecDepth 500000 in
lemma B_34_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 6 xs.toFinset) B_34_6 := by
  have hP := buildPoolsSubBT_sound (pdepth := 9) (W := W_34) (raw := r_34) (pspecs := ps_34) (used := [0,3,7,9,11,14,15,16,17,20,26,28,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128]) S_34_ok
  have hm0 := checkNodesBT_mem (by decide) gp_34 W_34_ok hP A_34_ok B_34_5_ok C_34_6_0
  have hm1 := checkNodesBT_mem (by decide) gp_34 W_34_ok hP A_34_ok B_34_5_ok C_34_6_1
  exact buildBucketsBT_of_mem (forall_append (hm0) hm1)
def P_34_7 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 r_34 S_34 ps_34 [0,3,14,33,34,35,40,41,42,44,45,46,48,50,53,59,60,63,69,71,75,80,84,87,90,92,97,98,104,105,107,108,119,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245]
def N_34_7 : List NodeSpec := [([39,30,0,1,2,3,4,5],[0,3],[0,1]),([39,0,1,2,132,3,4,5],[0],[0,1]),([89,39,0,1,2,3,4,5],[0],[0,1]),([0,1,2,3,42,4,5],[0,3,33,35,84,129],[0,1]),([40,39,0,1,2,3,4,5],[0,130,131,132,133],[0,1]),([107,39,0,1,2,3,4,5],[3,34],[0]),([39,0,1,198,2,3,4,5],[3,34,134],[0,1]),([104,0,1,2,3,4,6],[0,135,136],[0,1]),([104,0,1,2,3,4,8,5],[0,60,137],[0,1]),([142,147,0,1,2,3,4,5],[3],[0,1]),([104,0,1,2,3,175,4,5],[0],[0,1]),([0,1,2,3,4,5,141,228],[3,138],[0,1]),([0,1,2,3,217,4,5],[0,3,45,139],[0,1]),([165,104,0,1,2,3,4,5],[0,45],[0,1]),([0,1,2,3,4,5,211],[0,3,140],[0]),([104,0,1,2,3,4,5,6],[0],[0,1]),([243,0,1,2,3,4,5],[0,3,45,46,141],[]),([169,0,1,2,3,4,5],[0,3,34,45,46,142,143],[0]),([39,0,1,2,3,4,5,141],[3,45],[0]),([0,1,2,3,140,5,18],[3,144,145],[0,1]),([0,2,3,13,4,5],[0,98,119],[0,1]),([208,0,1,2,3,4,5,73],[50,87,146],[0]),([39,0,1,2,3,4,5,18],[3],[0]),([0,1,2,3,4,5,141,205],[0,147,148,149],[0,1]),([0,1,2,3,4,5,207],[0,3,150],[0,1]),([0,190,1,2,3,4,5],[0,3,151,152],[0,1]),([0,166,1,2,3,4,5],[0,3,153,154,155],[0,1]),([142,39,0,1,2,3,4,5],[3,45],[0]),([107,104,0,1,2,3,4,5],[3,34],[0]),([0,1,2,3,4,56,5],[0,3,108,156],[0,1]),([0,1,2,3,4,8,5,6],[0,3,60],[0]),([171,0,1,2,3,4,5,141],[33,45,148,157],[0,1]),([108,0,2,3,4,51,5],[0,3,33,34,158,159],[0]),([0,1,2,11,4,5,6],[0,63,160],[0,1]),([169,0,1,2,3,4,5,141],[3,45,142],[0]),([0,1,2,3,4,5,205],[0,3,161],[0,1]),([0,1,2,3,4,5,6,205],[0,160],[0,1]),([0,1,2,3,4,5,141,18],[3,145],[0,1]),([39,0,1,2,3,55,4,5],[0,3,45,130],[0,1]),([0,1,2,3,51,8,5],[0,3,80,162,163],[0,1]),([108,0,1,2,4,5,6],[0,160,164],[0,1]),([104,147,0,1,2,3,4,5],[33,153,165],[0,1]),([104,0,1,2,3,4,137,5],[34,59,153,166],[0,1]),([0,1,2,3,51,5,18],[3,104,167],[0,1]),([0,2,3,4,51,5,73],[0,3,50,168],[0,1]),([0,1,2,3,98,4,5],[0,3,169],[0,1]),([39,0,1,2,3,42,4,5],[0,170],[0,1]),([0,1,2,3,150,4,5],[0,3,171,172],[0,1]),([0,1,2,3,4,5,141,73],[148,173],[0,1]),([0,1,2,3,4,8,5,141],[0,3,97],[0,1]),([165,0,1,2,3,4,5],[0,3,34,46,84,174,175,176],[0,1]),([0,1,2,3,4,5,141,207],[0,148,177],[0,1]),([104,0,2,3,4,5,73],[0,33,50,178],[0,1]),([39,0,1,2,3,4,5],[0,3,45,46,179],[0]),([208,0,1,2,3,4,5],[0,3,45,46,180],[0,1]),([0,193,1,2,3,4,5],[3,84,131,181],[0,1]),([142,0,1,2,3,4,5],[3,34,46,84,182,183],[0,1]),([0,155,1,2,3,4,5],[0,3,33,45,184,185],[0,1]),([171,0,1,2,3,4,5],[0,3,34,45,46,148,157,186],[0]),([39,147,0,1,2,3,4,5],[3,131],[0,1]),([39,0,1,2,3,4,141],[3,45,131,187],[0]),([0,1,2,11,4,6],[0,63,128],[0,1]),([32,0,1,2,3,4,5,18],[0,3],[0]),([39,0,193,1,2,3,4,5],[3,131],[0]),([210,0,1,2,3,4,5,18],[0,3,145,188],[0,1]),([0,1,2,3,4,141,18],[3,189],[0,1]),([0,1,2,3,173,4,5,18],[0,3,104,190,191],[0,1]),([39,0,1,2,3,173,4,5],[0,3,170,192],[0,1]),([0,1,2,3,4,5,9],[34,84,193,194,195],[0,1]),([108,104,0,2,3,4,5],[0,196],[0]),([0,1,2,3,55,4,5,18],[0,3,45,188],[0,1]),([39,108,0,1,2,3,4,5],[0,3,170],[0]),([45,0,2,3,4,5],[0,41,42,44],[0,1]),([0,1,2,3,175,4,5],[0,3,197],[0,1]),([0,1,2,3,4,5,6,18],[0,3,191,198],[0,1]),([104,0,1,2,3,4,5,141],[0,45],[1]),([104,0,1,2,3,4,5,18],[3,104,153,191],[0]),([135,0,1,2,3,4,8,5],[0,80,163],[0]),([32,30,0,1,2,4],[0,40],[0,1]),([0,1,2,3,4,5,84],[0,3,199],[0]),([32,39,0,1,2,3,4,5],[0],[0]),([107,0,1,2,3,4,5],[0,3,45,46,200],[0]),([0,1,2,22,8,5],[0,105,107],[0]),([0,1,2,3,4,8,56,5],[0,3,97],[1]),([0,1,2,3,4,5,215],[0,34,84,201],[0,1]),([89,0,1,2,3,4,8,5],[],[0,1]),([39,0,1,2,11,3,4,5],[0,3,130,133],[0,1]),([45,0,1,2,3,4,5],[0,34,42,44,45,46],[0,1]),([135,0,1,2,3,4,5],[0,3,34,45,46,80,202],[0,1]),([32,0,1,2,4,8,5],[0,3,60,203,204],[0,1]),([0,1,2,3,4,5,199],[0,3,205],[0,1]),([0,1,2,3,8,5,18],[0,3,71,75,206,207],[0,1]),([39,0,1,2,3,4,8,5],[0,3],[0,1]),([0,1,2,3,4,14,5],[0,3,33,45,208],[0,1]),([39,0,1,2,3,4,5,73],[3,50,170],[0]),([39,104,0,1,2,3,4,5],[3,170,209],[0]),([0,1,2,3,4,14,8,5],[0,3,60,97,210],[0,1]),([152,0,1,2,3,4,5],[0,3,45,46,211],[0,1]),([0,1,2,3,4,8,5,9],[137,203,210],[0,1]),([88,0,1,2,3,4,5],[0,3,33,45,46,212,213,214],[0,1]),([88,0,1,2,3,4,8,5],[0,3],[0,1]),([39,0,1,2,3,5,18],[3,104,215],[0]),([0,1,2,3,4,5,6,215],[0,135],[0,1]),([89,0,1,2,3,4,5],[34,46,84,216],[0,1]),([0,1,2,3,4,5,141,6],[0,148,149,198],[0,1]),([210,115,0,1,2,5],[0,3,217],[0]),([210,0,1,2,4,5,6],[0,3,160,218],[0,1]),([210,39,0,1,2,3,4,5],[0,3,130,131],[0]),([0,1,3,12,4,5],[0,14,69],[0,1]),([0,1,2,3,77,5],[0,219,220],[0,1]),([0,1,2,3,4,69,5],[0,3,90,92],[0,1]),([0,164,2,3,4,5,73],[0,3,33,173,221],[0,1]),([244,0,1,2,4,5],[0,3,222,223],[]),([0,1,2,3,4,5,6,9],[3,160,224,225],[0,1]),([0,1,2,11,3,43,4,5],[0,3,226,227,228,229,230,231,232,233],[0,1]),([0,1,2,11,3,4,5,18],[3,145,188,191,228,234],[0,1]),([0,1,2,3,4,8,5],[0,3,235],[0,1]),([72,1,2,3,4,5,18],[0,3,48,145],[0,1]),([32,0,1,2,3,43,4,5],[0,236,237,238,239],[0,1]),([0,2,3,173,4,5,73],[0,240],[0,1]),([0,1,2,3,192,4,5],[0,3,241],[0,1]),([39,147,0,1,2,3,4],[3,45,131,242],[0]),([152,0,1,2,3,4,5,18],[3,104],[0,1]),([45,0,2,3,4,5,6],[0,44,53],[0,1]),([39,0,1,2,3,4,5,6],[0,170],[0,1]),([0,1,2,50,3,4,5,18],[0,3],[0,1]),([70,0,1,2,3,4,5,18],[0,145,188],[0]),([104,0,166,1,2,3,4,5],[153,154],[0,1]),([46,0,1,2,3,4,5],[0,3,34,45,46,243,244],[0,1]),([108,0,1,2,3,4,5,18],[0,3,104,191],[0,1]),([46,0,1,2,3,4,5,6],[0,3],[0,1]),([0,1,2,3,4,5,6],[0,3,245],[0,1]),([32,30,0,1,2,4,5],[0,40],[0,1]),([45,0,1,2,3,4,5,6],[0,135],[0,1]),([32,38,0,1,2,3,4,5],[0,3],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_7 : checkNodesBT W_34 g_34 F_34 P_34_7 A_34 B_34_6 7 N_34_7 = true := by decide +kernel
def B_34_7 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_7
set_option maxRecDepth 500000 in
lemma B_34_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 7 xs.toFinset) B_34_7 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound S_34_ok) A_34_ok B_34_6_ok C_34_7
def P_34_8 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 r_34 S_34 ps_34 [0,3,33,34,45,46,84,97,130,131,132,133,137,148,153,160,170,190,198,203,209,210,224,225,228,233,236,239,246,247,248,249,250,251,252,253,254,255,256]
def N_34_8 : List NodeSpec := [([39,0,1,2,3,4,5],[0,3,34,45,46,130,131,132,133,170],[0,1]),([0,1,2,3,4,5,6],[0,3,33,160,198,224,225],[0,1]),([0,1,2,11,3,4,5],[0,3,33,45,84,228,233],[0,1]),([0,1,2,3,4,8,5],[0,3,97,137,203,210],[0,1]),([210,0,1,2,3,4,5],[0,3,45,84,246,247],[0,1]),([104,0,1,2,3,4,5],[0,3,33,34,45,46,153,209,248],[0,1]),([0,1,2,22,3,4,5],[0,3,249,250],[0]),([0,1,2,3,4,5,141],[0,3,45,148,251],[0,1]),([108,0,1,2,3,4,5],[0,3,33,34,45,84,252,253],[0,1]),([0,1,2,3,173,4,5],[0,3,33,34,190,254],[0,1]),([0,1,2,3,55,4,5],[0,3,45,255],[0,1]),([32,0,1,2,3,4,5],[0,3,45,84,236,239],[0,1]),([0,1,164,2,3,4,5],[0,3,33,45,256],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_8 : checkNodesBT W_34 g_34 F_34 P_34_8 A_34 B_34_7 8 N_34_8 = true := by decide +kernel
def B_34_8 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_8
set_option maxRecDepth 500000 in
lemma B_34_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 8 xs.toFinset) B_34_8 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound S_34_ok) A_34_ok B_34_7_ok C_34_8
def P_34_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_34 r_34 S_34 ps_34 [33,34,45,46,84]
def N_34_9 : List NodeSpec := [([0,1,2,3,4,5],[33,34,45,46,84],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_34_9 : checkNodesBT W_34 g_34 F_34 P_34_9 A_34 B_34_8 9 N_34_9 = true := by decide +kernel
def B_34_9 : BT (List (List Nat)) := buildBucketsBT W_34 N_34_9
set_option maxRecDepth 500000 in
lemma B_34_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_34 9 xs.toFinset) B_34_9 :=
  buildBucketsBT_sound (by decide) gp_34 W_34_ok (buildPoolsSubBT_sound S_34_ok) A_34_ok B_34_8_ok C_34_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_34_ok : forestRootCheck r_34 g_34 [(VAR 0,16,17),(VAR 1,8,10),(VAR 2,8,12),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,1,33)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_34_in : bucketContainsBT B_34_9 r_34 = true := by decide +kernel
lemma low_34 : Lower r_34 g_34 10 := lower_of_forestBT root_34_ok B_34_9_ok root_34_in
def g_35 := 0xfffeffeefffcf000fffeffeefffcf000fffeffeefffcf000fffeffeefffcf000
def r_35 : List Nat := varsOf 63
set_option maxHeartbeats 0 in
lemma low_35 : Lower r_35 g_35 8 := by
  have hc : Lower (varsOf 61) 0xfffaffaafff0f000fffaffaafff0f000fffaffaafff0f000fffaffaafff0f000 7 := carry_of (swaps := [(1,5),(2,5),(3,4),(4,5)]) (by decide +kernel) low_9
  exact lift_of_f (z := 2) (o := 0) (essPairs := [(VAR 1,16,18)]) (by decide +kernel) hc
def g_36 := 0xfffefffafffcf000fffefffafffcf000fffefffafffcf000fffefffafffcf000
def r_36 : List Nat := varsOf 63
set_option maxHeartbeats 0 in
lemma low_36 : Lower r_36 g_36 8 := by
  have hc : Lower (varsOf 62) 0xfffcfff0fffcf000fffcfff0fffcf000fffcfff0fffcf000fffcfff0fffcf000 7 := carry_of (swaps := [(0,5),(1,5)]) (by decide +kernel) low_8
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,32,33)]) (by decide +kernel) hc
def g_37 := 0xfffeeac0fffeeac0fffeeac0fffeeac0fffeeac0fffeeac0fffeeac0fffeeac0
def r_37 : List Nat := varsOf 31
def p_37 : List Nat := [6,6,7,7,9,9,11,11,13,13,14,14,17,17,18,18,19,20,20,21,24,24,26,28]
def q_37 : List Nat := [4,2,5,3,8,1,10,3,12,5,12,10,16,1,16,2,3,16,4,5,16,8,10,12]
def F_37 : Nat := fullMask 24
set_option maxHeartbeats 0 in
lemma gp_37 : goodPairs g_37 p_37 q_37 := goodPairs_of (by decide +kernel)
def W_37 : BT Decor := buildWiresBT 3 (mkBase p_37 q_37 r_37) []
lemma W_37_ok : btAll (fun x => faithful p_37 q_37 x ∧ x.1 < 2^256) W_37 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_37 : List (List (Nat × Nat)) := [[]]
def A_37 : BT (List (Nat × Nat)) := btOfList 1 al_37
set_option maxHeartbeats 0 in
lemma A_37_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_37 = g_37) A_37 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_37_0 : Slice r_37 g_37 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 30) 0xfffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0fffcc0c0 5 := carry_of (swaps := [(0,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_1 : Slice r_37 g_37 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 29) 0xfffaaa00fffaaa00fffaaa00fffaaa00fffaaa00fffaaa00fffaaa00fffaaa00 5 := carry_of (swaps := [(0,1),(1,4),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_2 : Slice r_37 g_37 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 27) 0xffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00ffeeaa00 5 := carry_of (swaps := [(0,1),(2,4),(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_37_3 : Slice r_37 g_37 (subcubeFast 8 0) 5 := by
  have hc : Lower (varsOf 23) 0xfefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0fefec0c0 5 := carry_of (swaps := [(3,4)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
def S_37 : BT (Option (Nat × Nat)) := btOfList 2 [some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 8 0,5)]
lemma S_37_ok : btAll (fun o => ∀ p, o = some p → Slice r_37 g_37 p.1 p.2) S_37 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_37_0) (forall_cons (fun _ h => by cases h; exact sl_37_1) (forall_cons (fun _ h => by cases h; exact sl_37_2) (forall_cons (fun _ h => by cases h; exact sl_37_3) (fun _ h => (List.not_mem_nil h).elim)))))
def ps_37 : BT (Option PoolSpec) := btOfList 2 ((([(0,[]),(1,[]),(2,[]),(3,[])] : List PoolSpec)).map some)
def B_37_5 : BT (List (List Nat)) := BT.empty
lemma B_37_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_37 5 xs.toFinset) B_37_5 := .empty
def P_37_6 : BT (Option BoundPool) := buildPoolsSubBT 2 W_37 r_37 S_37 ps_37 [0,1,2,3]
def N_37_6 : List NodeSpec := [([0,1,2,3,4],[0,1,2,3],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_37_6 : checkNodesBT W_37 g_37 F_37 P_37_6 A_37 B_37_5 6 N_37_6 = true := by decide +kernel
def B_37_6 : BT (List (List Nat)) := buildBucketsBT W_37 N_37_6
set_option maxRecDepth 500000 in
lemma B_37_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_37 6 xs.toFinset) B_37_6 :=
  buildBucketsBT_sound (by decide) gp_37 W_37_ok (buildPoolsSubBT_sound S_37_ok) A_37_ok B_37_5_ok C_37_6
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_37_ok : forestRootCheck r_37 g_37 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9),(VAR 4,1,17)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_37_in : bucketContainsBT B_37_6 r_37 = true := by decide +kernel
lemma low_37 : Lower r_37 g_37 7 := lower_of_forestBT root_37_ok B_37_6_ok root_37_in
def g_38 := 0xfefafc00fefafc00fefafc00fefafc00fefafc00fefafc00fefafc00fefafc00
def r_38 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_38 : Lower r_38 g_38 5 := by
  have hc : Lower (varsOf 30) 0xfcf0fc00fcf0fc00fcf0fc00fcf0fc00fcf0fc00fcf0fc00fcf0fc00fcf0fc00 4 := carry_of (swaps := [(0,4),(1,4)]) (by decide +kernel) low_7
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_39 := 0xfefefeeefefafc00fefefeeefefafc00fefefeeefefafc00fefefeeefefafc00
def r_39 : List Nat := varsOf 63
def p_39 : List Nat := [10,10,11,11,12,12,13,13,14,15,17,17,19,19,20,20,21,22,22,23,25,25,26,26,28,33,33,34,34,35,37,37,38,38,39,41,41,42,44,44,49,50,50,52,52,57,58,60]
def q_39 : List Nat := [8,2,9,3,8,4,9,5,6,7,16,1,18,3,16,4,5,18,6,7,24,9,24,18,24,32,1,32,2,3,36,5,36,6,7,40,9,40,40,36,48,48,18,48,36,56,56,56]
def F_39 : Nat := fullMask 48
set_option maxHeartbeats 0 in
lemma gp_39 : goodPairs g_39 p_39 q_39 := goodPairs_of (by decide +kernel)
def W_39 : BT Decor := buildWiresBT 3 (mkBase p_39 q_39 r_39) [(1,0,1),(2,6,5)]
lemma W_39_ok : btAll (fun x => faithful p_39 q_39 x ∧ x.1 < 2^256) W_39 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_39 : List (List (Nat × Nat)) := [[],[(1,2),(4,5)],[(0,2),(1,2),(3,5),(4,5)],[(0,3),(1,4),(2,5)],[(0,3),(1,5),(2,4)],[(0,5),(1,3),(2,4),(3,4),(4,5)]]
def A_39 : BT (List (Nat × Nat)) := btOfList 3 al_39
set_option maxHeartbeats 0 in
lemma A_39_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_39 = g_39) A_39 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_39_0 : Slice r_39 g_39 (identDom 0 3) 7 := by
  have hc : Lower (varsOf 55) 0xfefeeeeefafaa8a8fefeeeeefafaa8a8fefeeeeefafaa8a8fefeeeeefafaa8a8 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,5)]) (by decide +kernel) low_37
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_1 : Slice r_39 g_39 (identDom 1 4) 7 := by
  have hc : Lower (varsOf 47) 0xfeeefeeefcc8fcc8feeefeeefcc8fcc8feeefeeefcc8fcc8feeefeeefcc8fcc8 7 := carry_of (swaps := [(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_37
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_2 : Slice r_39 g_39 (identDom 2 5) 7 := by
  have hc : Lower (varsOf 31) 0xfefafce0fefafce0fefafce0fefafce0fefafce0fefafce0fefafce0fefafce0 7 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_37
  exact slice_ident (u := 2) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_3 : Slice r_39 g_39 (subcubeFast 1 0) 5 := by
  have hc : Lower (varsOf 62) 0xfcfcfcccfcf0fc00fcfcfcccfcf0fc00fcfcfcccfcf0fc00fcfcfcccfcf0fc00 5 := carry_of (swaps := [(0,5),(1,3),(2,4),(3,4),(4,5)]) (by decide +kernel) low_38
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_4 : Slice r_39 g_39 (subcubeFast 2 0) 5 := by
  have hc : Lower (varsOf 61) 0xfafafaaafafaf000fafafaaafafaf000fafafaaafafaf000fafafaaafafaf000 5 := carry_of (swaps := [(0,3),(1,5),(2,4)]) (by decide +kernel) low_38
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_5 : Slice r_39 g_39 (subcubeFast 4 0) 5 := by
  have hc : Lower (varsOf 59) 0xeeeeeeeeeeaacc00eeeeeeeeeeaacc00eeeeeeeeeeaacc00eeeeeeeeeeaacc00 5 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_38
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_6 : Slice r_39 g_39 (subcubeFast 32 0) 5 := by
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) low_38
set_option maxHeartbeats 0 in
lemma sl_39_7 : Slice r_39 g_39 (subcubeFast 17 0) 4 := by
  have hc : Lower (varsOf 46) 0xfcccfcccfc00fc00fcccfcccfc00fc00fcccfcccfc00fc00fcccfcccfc00fc00 4 := carry_of (swaps := [(0,4),(1,2),(2,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 17) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_8 : Slice r_39 g_39 (subcubeFast 33 0) 4 := by
  have hc : Lower (varsOf 30) 0xfcf0fc00fcf0fc00fcf0fc00fcf0fc00fcf0fc00fcf0fc00fcf0fc00fcf0fc00 4 := carry_of (swaps := [(0,4),(1,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 33) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_9 : Slice r_39 g_39 (subcubeFast 10 0) 4 := by
  have hc : Lower (varsOf 53) 0xfafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000 4 := carry_of (swaps := [(0,2),(1,4),(3,5),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 10) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_10 : Slice r_39 g_39 (subcubeFast 34 0) 4 := by
  have hc : Lower (varsOf 29) 0xfafaf000fafaf000fafaf000fafaf000fafaf000fafaf000fafaf000fafaf000 4 := carry_of (swaps := [(1,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 34) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_11 : Slice r_39 g_39 (subcubeFast 12 0) 4 := by
  have hc : Lower (varsOf 51) 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000 4 := carry_of (swaps := [(0,2),(1,2),(2,4),(3,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 12) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_39_12 : Slice r_39 g_39 (subcubeFast 20 0) 4 := by
  have hc : Lower (varsOf 43) 0xeeeeeeeecc00cc00eeeeeeeecc00cc00eeeeeeeecc00cc00eeeeeeeecc00cc00 4 := carry_of (swaps := [(1,2),(2,4),(3,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 20) (o := 0) (by decide +kernel) hc
def S_39 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 3,7),some (identDom 1 4,7),some (identDom 2 5,7),some (subcubeFast 1 0,5),some (subcubeFast 2 0,5),some (subcubeFast 4 0,5),some (subcubeFast 32 0,5),some (subcubeFast 17 0,4),some (subcubeFast 33 0,4),some (subcubeFast 10 0,4),some (subcubeFast 34 0,4),some (subcubeFast 12 0,4),some (subcubeFast 20 0,4)]
lemma S_39_ok : btAll (fun o => ∀ p, o = some p → Slice r_39 g_39 p.1 p.2) S_39 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_39_0) (forall_cons (fun _ h => by cases h; exact sl_39_1) (forall_cons (fun _ h => by cases h; exact sl_39_2) (forall_cons (fun _ h => by cases h; exact sl_39_3) (forall_cons (fun _ h => by cases h; exact sl_39_4) (forall_cons (fun _ h => by cases h; exact sl_39_5) (forall_cons (fun _ h => by cases h; exact sl_39_6) (forall_cons (fun _ h => by cases h; exact sl_39_7) (forall_cons (fun _ h => by cases h; exact sl_39_8) (forall_cons (fun _ h => by cases h; exact sl_39_9) (forall_cons (fun _ h => by cases h; exact sl_39_10) (forall_cons (fun _ h => by cases h; exact sl_39_11) (forall_cons (fun _ h => by cases h; exact sl_39_12) (fun _ h => (List.not_mem_nil h).elim))))))))))))))
def ps_39 : BT (Option PoolSpec) := btOfList 4 ((([(3,[]),(6,[]),(4,[]),(5,[]),(0,[]),(7,[]),(8,[]),(9,[]),(1,[]),(10,[]),(11,[]),(12,[]),(2,[])] : List PoolSpec)).map some)
def B_39_4 : BT (List (List Nat)) := BT.empty
lemma B_39_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_39 4 xs.toFinset) B_39_4 := .empty
def P_39_5 : BT (Option BoundPool) := buildPoolsSubBT 4 W_39 r_39 S_39 ps_39 []
def N_39_5 : List NodeSpec := [([7,0,1,2,3,4],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_39_5 : checkNodesBT W_39 g_39 F_39 P_39_5 A_39 B_39_4 5 N_39_5 = true := by decide +kernel
def B_39_5 : BT (List (List Nat)) := buildBucketsBT W_39 N_39_5
set_option maxRecDepth 500000 in
lemma B_39_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_39 5 xs.toFinset) B_39_5 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound S_39_ok) A_39_ok B_39_4_ok C_39_5
def P_39_6 : BT (Option BoundPool) := buildPoolsSubBT 4 W_39 r_39 S_39 ps_39 [0,1]
def N_39_6 : List NodeSpec := [([0,1,6,2,3,4,5],[0,1],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_39_6 : checkNodesBT W_39 g_39 F_39 P_39_6 A_39 B_39_5 6 N_39_6 = true := by decide +kernel
def B_39_6 : BT (List (List Nat)) := buildBucketsBT W_39 N_39_6
set_option maxRecDepth 500000 in
lemma B_39_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_39 6 xs.toFinset) B_39_6 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound S_39_ok) A_39_ok B_39_5_ok C_39_6
def P_39_7 : BT (Option BoundPool) := buildPoolsSubBT 4 W_39 r_39 S_39 ps_39 [0,2,3,4,5,6,7,8,9,10,11,12]
def N_39_7 : List NodeSpec := [([0,1,2,3,4,5],[0,2,3,4,5,6,7,8,9,10,11,12],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_39_7 : checkNodesBT W_39 g_39 F_39 P_39_7 A_39 B_39_6 7 N_39_7 = true := by decide +kernel
def B_39_7 : BT (List (List Nat)) := buildBucketsBT W_39 N_39_7
set_option maxRecDepth 500000 in
lemma B_39_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_39 7 xs.toFinset) B_39_7 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok (buildPoolsSubBT_sound S_39_ok) A_39_ok B_39_6_ok C_39_7
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_39_ok : forestRootCheck r_39 g_39 [(VAR 0,16,17),(VAR 1,8,10),(VAR 2,8,12),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,1,33)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_39_in : bucketContainsBT B_39_7 r_39 = true := by decide +kernel
lemma low_39 : Lower r_39 g_39 8 := lower_of_forestBT root_39_ok B_39_7_ok root_39_in
def g_40 := 0xfffffffffffffff0fefefeeefefafc00fffffffffffffff0fefefeeefefafc00
def r_40 : List Nat := varsOf 127
def p_40 : List Nat := [10,10,11,11,12,12,13,13,14,15,17,17,19,19,20,20,21,22,22,23,25,25,26,26,28,33,33,34,34,35,37,37,38,38,39,41,41,42,44,44,49,50,50,52,52,57,58,60,68,68,69,69,70,70,71,71,72,72,73,73,74,75,80,80,81,82,82,83,88,96,96,97,98,99,100,104,112,120]
def q_40 : List Nat := [8,2,9,3,8,4,9,5,6,7,16,1,18,3,16,4,5,18,6,7,24,9,24,18,24,32,1,32,2,3,36,5,36,6,7,40,9,40,40,36,48,48,18,48,36,56,56,56,64,4,65,5,66,6,67,7,64,8,65,9,66,67,64,16,65,66,18,67,24,64,32,65,66,67,36,40,48,56]
def F_40 : Nat := fullMask 78
set_option maxHeartbeats 0 in
lemma gp_40 : goodPairs g_40 p_40 q_40 := goodPairs_of (by decide +kernel)
def W_40 : BT Decor := buildWiresBT 7 (mkBase p_40 q_40 r_40) [(1,3,4),(1,7,5),(1,8,6),(3,2,9),(1,2,3),(1,4,5),(1,11,12),(2,13,6),(2,7,6),(1,3,5),(1,3,6),(1,4,17),(3,2,18),(1,11,4),(1,1,6),(1,2,4),(2,22,6),(1,23,5),(3,2,7),(1,2,6),(0,2,17),(1,27,4),(2,11,6),(1,0,6),(2,2,6),(3,31,20),(1,5,6),(1,4,33),(1,23,3),(2,20,6),(2,2,4),(0,2,7),(1,38,6),(1,4,6),(3,4,33),(1,41,3),(3,2,33),(1,43,3),(3,4,17),(1,45,5),(1,16,6),(3,2,47),(1,41,2),(3,1,16),(1,50,6),(3,4,47),(0,2,18),(3,5,40),(1,54,3),(2,7,5),(1,56,2),(3,2,8),(3,2,17),(1,59,5),(1,25,6),(3,2,40),(1,62,3),(1,31,3),(1,64,5),(1,31,4),(3,4,26),(1,67,5),(2,8,6),(1,64,4),(1,29,5),(1,22,6),(3,4,21),(1,73,2),(2,11,5),(1,25,5),(1,37,3),(1,77,5),(3,2,21),(1,79,4),(2,11,4),(1,56,6),(1,15,5),(3,5,17),(3,5,18),(1,73,0),(1,37,6),(1,5,87),(0,2,21),(1,0,89),(1,15,2),(2,37,3),(1,92,4),(2,20,5),(1,11,33),(1,20,6),(1,81,5),(2,22,5),(1,98,3),(1,11,6),(3,2,30),(2,37,6),(3,5,26)]
lemma W_40_ok : btAll (fun x => faithful p_40 q_40 x ∧ x.1 < 2^256) W_40 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_40 : List (List (Nat × Nat)) := [[],[(0,1),(3,4)]]
def A_40 : BT (List (Nat × Nat)) := btOfList 1 al_40
set_option maxHeartbeats 0 in
lemma A_40_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_40 = g_40) A_40 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_40_0 : Slice r_40 g_40 (identDom 0 3) 10 := by
  have hc : Lower (varsOf 119) 0xfffffffffffffafafefeeeeefafaa8a8fffffffffffffafafefeeeeefafaa8a8 10 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,6),(4,5),(5,6)]) (by decide +kernel) low_33
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_1 : Slice r_40 g_40 (identDom 1 4) 10 := by
  have hc : Lower (varsOf 111) 0xfffffffffffcfffcfeeefeeefcc8fcc8fffffffffffcfffcfeeefeeefcc8fcc8 10 := carry_of (swaps := [(1,5),(2,5),(3,5),(4,6)]) (by decide +kernel) low_33
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_2 : Slice r_40 g_40 (subcubeFast 2 0) 9 := by
  have hc : Lower (varsOf 125) 0xfffffffffffffff0fafafaaafafaf000fffffffffffffff0fafafaaafafaf000 9 := carry_of (swaps := [(0,3),(1,6),(2,4),(5,6)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_3 : Slice r_40 g_40 (subcubeFast 1 0) 9 := by
  have hc : Lower (varsOf 126) 0xfffffffffffffff0fcfcfcccfcf0fc00fffffffffffffff0fcfcfcccfcf0fc00 9 := carry_of (swaps := [(0,6),(1,3),(2,4),(3,4),(4,6),(5,6)]) (by decide +kernel) low_20
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_4 : Slice r_40 g_40 (identDom 2 5) 10 := by
  have hc : Lower (varsOf 95) 0xfffffff0fffffff0fefafce0fefafce0fffffff0fffffff0fefafce0fefafce0 10 := carry_of (swaps := [(2,5),(5,6)]) (by decide +kernel) low_34
  exact slice_ident (u := 2) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_5 : Slice r_40 g_40 (subcubeFast 8 0) 8 := by
  have hc : Lower (varsOf 119) 0xfffffffffffff0f0fefeeeeefafa0000fffffffffffff0f0fefeeeeefafa0000 8 := carry_of (swaps := [(0,1),(3,6)]) (by decide +kernel) low_35
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_6 : Slice r_40 g_40 (subcubeFast 16 0) 8 := by
  have hc : Lower (varsOf 111) 0xfffffffffff0fff0feeefeeefc00fc00fffffffffff0fff0feeefeeefc00fc00 8 := carry_of (swaps := [(3,4),(4,6)]) (by decide +kernel) low_35
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_7 : Slice r_40 g_40 (subcubeFast 32 0) 8 := by
  have hc : Lower (varsOf 95) 0xfffffff0fffffff0fefafc00fefafc00fffffff0fffffff0fefafc00fefafc00 8 := carry_of (swaps := [(3,4),(4,5),(5,6)]) (by decide +kernel) low_36
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_8 : Slice r_40 g_40 (subcubeFast 64 0) 8 := by
  exact slice_fast_direct_f (z := 64) (o := 0) (by decide +kernel) low_39
set_option maxHeartbeats 0 in
lemma sl_40_9 : Slice r_40 g_40 (subcubeFast 8 2) 6 := by
  have hc : Lower (varsOf 117) 0xfffffffffffff0f0fffffffffafa0000fffffffffffff0f0fffffffffafa0000 6 := carry_of (swaps := [(1,5),(2,5),(3,6),(4,6),(5,6)]) (by decide +kernel) low_31
  exact slice_fast_direct_f (z := 8) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_10 : Slice r_40 g_40 (subcubeFast 32 1) 6 := by
  have hc : Lower (varsOf 94) 0xfffffff0fffffff0fffffc00fffffc00fffffff0fffffff0fffffc00fffffc00 6 := carry_of (swaps := [(0,5),(1,5),(2,5),(5,6)]) (by decide +kernel) low_31
  exact slice_fast_direct_f (z := 32) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_11 : Slice r_40 g_40 (subcubeFast 16 1) 6 := by
  have hc : Lower (varsOf 110) 0xfffffffffff0fff0fffffffffc00fc00fffffffffff0fff0fffffffffc00fc00 6 := carry_of (swaps := [(0,5),(1,5),(2,5),(4,6),(5,6)]) (by decide +kernel) low_31
  exact slice_fast_direct_f (z := 16) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_12 : Slice r_40 g_40 (subcubeFast 32 2) 6 := by
  have hc : Lower (varsOf 93) 0xfffffff0fffffff0fffaff00fffaff00fffffff0fffffff0fffaff00fffaff00 6 := carry_of (swaps := [(1,5),(2,5),(3,4),(5,6)]) (by decide +kernel) low_31
  exact slice_fast_direct_f (z := 32) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_13 : Slice r_40 g_40 (subcubeFast 40 2) 5 := by
  have hc : Lower (varsOf 85) 0xfffff0f0fffff0f0fafa0000fafa0000fffff0f0fffff0f0fafa0000fafa0000 5 := carry_of (swaps := [(1,4),(2,4),(3,5),(4,5),(5,6)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 40) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_14 : Slice r_40 g_40 (subcubeFast 48 1) 5 := by
  have hc : Lower (varsOf 78) 0xfff0fff0fff0fff0fc00fc00fc00fc00fff0fff0fff0fff0fc00fc00fc00fc00 5 := carry_of (swaps := [(0,4),(1,4),(2,4),(4,5),(5,6)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 48) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_15 : Slice r_40 g_40 (subcubeFast 26 0) 4 := by
  have hc : Lower (varsOf 101) 0xfffffffff0f0f0f0aaaaaaaa00000000fffffffff0f0f0f0aaaaaaaa00000000 4 := carry_of (swaps := [(1,4),(2,4),(3,5),(4,6)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 26) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_16 : Slice r_40 g_40 (subcubeFast 84 0) 4 := by
  have hc : Lower (varsOf 43) 0xeeeeeeeecc00cc00eeeeeeeecc00cc00eeeeeeeecc00cc00eeeeeeeecc00cc00 4 := carry_of (swaps := [(1,2),(2,4),(3,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 84) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_17 : Slice r_40 g_40 (subcubeFast 76 0) 4 := by
  have hc : Lower (varsOf 51) 0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000 4 := carry_of (swaps := [(0,2),(1,2),(2,4),(3,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 76) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_18 : Slice r_40 g_40 (subcubeFast 98 0) 4 := by
  have hc : Lower (varsOf 29) 0xfafaf000fafaf000fafaf000fafaf000fafaf000fafaf000fafaf000fafaf000 4 := carry_of (swaps := [(1,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 98) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_19 : Slice r_40 g_40 (subcubeFast 38 0) 4 := by
  have hc : Lower (varsOf 89) 0xffffff00ffffff00aaaa0000aaaa0000ffffff00ffffff00aaaa0000aaaa0000 4 := carry_of (swaps := [(1,4),(2,5),(3,4),(5,6)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 38) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_40_20 : Slice r_40 g_40 (subcubeFast 97 0) 4 := by
  have hc : Lower (varsOf 30) 0xfcf0fc00fcf0fc00fcf0fc00fcf0fc00fcf0fc00fcf0fc00fcf0fc00fcf0fc00 4 := carry_of (swaps := [(0,4),(1,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 97) (o := 0) (by decide +kernel) hc
def S_40 : BT (Option (Nat × Nat)) := btOfList 5 [some (identDom 0 3,10),some (identDom 1 4,10),some (subcubeFast 2 0,9),some (subcubeFast 1 0,9),some (identDom 2 5,10),some (subcubeFast 8 0,8),some (subcubeFast 16 0,8),some (subcubeFast 32 0,8),some (subcubeFast 64 0,8),some (subcubeFast 8 2,6),some (subcubeFast 32 1,6),some (subcubeFast 16 1,6),some (subcubeFast 32 2,6),some (subcubeFast 40 2,5),some (subcubeFast 48 1,5),some (subcubeFast 26 0,4),some (subcubeFast 84 0,4),some (subcubeFast 76 0,4),some (subcubeFast 98 0,4),some (subcubeFast 38 0,4),some (subcubeFast 97 0,4)]
lemma S_40_ok : btAll (fun o => ∀ p, o = some p → Slice r_40 g_40 p.1 p.2) S_40 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_40_0) (forall_cons (fun _ h => by cases h; exact sl_40_1) (forall_cons (fun _ h => by cases h; exact sl_40_2) (forall_cons (fun _ h => by cases h; exact sl_40_3) (forall_cons (fun _ h => by cases h; exact sl_40_4) (forall_cons (fun _ h => by cases h; exact sl_40_5) (forall_cons (fun _ h => by cases h; exact sl_40_6) (forall_cons (fun _ h => by cases h; exact sl_40_7) (forall_cons (fun _ h => by cases h; exact sl_40_8) (forall_cons (fun _ h => by cases h; exact sl_40_9) (forall_cons (fun _ h => by cases h; exact sl_40_10) (forall_cons (fun _ h => by cases h; exact sl_40_11) (forall_cons (fun _ h => by cases h; exact sl_40_12) (forall_cons (fun _ h => by cases h; exact sl_40_13) (forall_cons (fun _ h => by cases h; exact sl_40_14) (forall_cons (fun _ h => by cases h; exact sl_40_15) (forall_cons (fun _ h => by cases h; exact sl_40_16) (forall_cons (fun _ h => by cases h; exact sl_40_17) (forall_cons (fun _ h => by cases h; exact sl_40_18) (forall_cons (fun _ h => by cases h; exact sl_40_19) (forall_cons (fun _ h => by cases h; exact sl_40_20) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))
def ps_40 : BT (Option PoolSpec) := btOfList 9 ((([(8,[]),(16,[]),(19,[]),(14,[]),(3,[(1,3,4),(1,3,5)]),(5,[]),(4,[(1,1,6),(1,5,6)]),(14,[(1,1,6)]),(3,[(1,3,6),(0,2,17),(1,27,4)]),(0,[(1,3,6),(0,2,17),(1,27,4)]),(8,[(0,2,17),(1,27,4)]),(7,[]),(8,[(1,3,5),(3,1,16)]),(9,[]),(5,[(1,7,6),(0,2,18)]),(8,[(1,3,4),(3,2,18)]),(4,[]),(13,[]),(6,[]),(6,[(1,3,6),(3,2,17)]),(15,[]),(5,[(1,7,6),(3,2,18)]),(0,[(1,4,3),(1,4,5),(1,3,5)]),(3,[(1,4,3),(1,4,5),(1,3,5)]),(1,[(1,4,3),(1,4,5),(1,3,5)]),(2,[(1,4,3),(1,4,5),(1,3,5)]),(4,[(1,4,3),(1,4,5),(1,3,5)]),(8,[(1,4,3),(3,2,7)]),(2,[]),(8,[(1,3,4),(3,2,7)]),(5,[(0,2,7),(1,38,6)]),(4,[(1,3,4),(0,2,7),(1,38,6)]),(5,[(1,4,6),(3,2,40)]),(5,[(1,4,17),(3,2,18)]),(3,[(1,2,3),(1,3,4)]),(4,[(1,2,3),(1,3,4),(1,4,5)]),(6,[(1,3,5),(3,1,16)]),(0,[]),(10,[]),(1,[]),(3,[(1,2,4),(1,2,6),(1,4,6)]),(4,[(1,2,4),(1,2,6),(1,4,6)]),(2,[(1,4,5),(1,4,6)]),(3,[]),(7,[(1,1,6)]),(14,[(3,1,16)]),(17,[]),(5,[(1,1,6)]),(4,[(1,1,6),(1,2,3),(1,3,6)]),(3,[(1,1,6),(1,3,4),(1,3,6)]),(6,[(1,1,6),(1,3,6)]),(4,[(1,2,6),(1,4,5),(1,4,6)]),(0,[(1,0,6)]),(3,[(1,1,6),(1,4,5),(1,5,6)]),(4,[(1,1,6),(1,4,5),(1,5,6)]),(18,[]),(2,[(1,3,4),(1,4,6)]),(3,[(1,2,6),(3,4,26)]),(6,[(1,1,6),(1,73,0)]),(8,[(3,4,21),(1,73,0)]),(9,[(1,73,0)]),(3,[(1,3,5)]),(9,[(1,0,89)]),(10,[(1,1,6)]),(3,[(1,4,3)]),(6,[(1,1,6),(1,5,6)]),(4,[(1,1,6),(1,2,4),(1,5,6)]),(3,[(1,1,6),(1,5,6)]),(4,[(1,5,6)]),(3,[(1,5,6),(3,4,33)]),(2,[(1,5,6),(3,4,33)]),(6,[(1,5,6)]),(4,[(1,5,6),(3,4,33)]),(2,[(1,5,6)]),(3,[(1,5,6),(3,2,33)]),(2,[(1,5,6),(3,2,33)]),(4,[(1,5,6),(3,2,33)]),(3,[(1,3,6),(3,5,17)]),(2,[(1,3,6),(3,5,17)]),(7,[(1,3,6)]),(5,[(1,4,17)]),(3,[(1,3,6),(0,2,17)]),(5,[(0,2,17)]),(8,[(1,3,5)]),(0,[(1,3,5),(1,16,6)]),(3,[(1,3,5),(1,16,6)]),(2,[(1,3,5),(1,16,6)]),(4,[(1,3,5),(1,16,6)]),(0,[(1,3,5),(1,5,6)]),(3,[(1,3,5),(1,5,6)]),(2,[(1,3,5),(1,5,6)]),(4,[(1,3,5),(1,5,6)]),(0,[(1,3,5),(1,4,5)]),(3,[(1,3,5),(1,4,5)]),(2,[(1,3,5),(1,4,5)]),(4,[(1,3,5),(1,4,5)]),(4,[(1,2,3),(1,5,6)]),(3,[(1,1,6)]),(3,[(1,1,6),(2,2,4)]),(6,[(1,1,6)]),(4,[(1,1,6)]),(2,[(2,2,4)]),(3,[(1,4,5),(1,4,6)]),(1,[(1,4,5),(1,4,6)]),(4,[(1,4,5),(1,4,6)]),(8,[(1,4,5)]),(2,[(1,4,6)]),(5,[(1,4,6)]),(3,[(1,2,3),(2,11,4)]),(2,[(1,2,3),(2,11,4)]),(5,[(2,11,4)]),(6,[(1,2,3)]),(8,[(1,2,3)]),(0,[(1,2,3),(1,11,6)]),(3,[(1,2,3),(1,11,6)]),(2,[(1,2,3),(1,11,6)]),(4,[(1,2,3),(1,11,6)]),(3,[(1,2,3),(2,11,6)]),(2,[(1,2,3),(2,11,6)]),(5,[(2,11,6)]),(6,[(1,2,6)]),(4,[(1,2,6)]),(3,[(2,2,4),(1,2,6)]),(0,[(1,1,6)]),(0,[(1,1,6),(1,2,3)]),(3,[(1,1,6),(1,2,3)]),(4,[(1,1,6),(1,2,3)]),(3,[(2,2,4),(2,37,3)]),(2,[(2,2,4),(2,37,3)]),(5,[(2,2,4)]),(3,[(1,1,6),(1,4,5)]),(4,[(1,1,6),(1,4,5)]),(1,[(1,1,6),(1,4,5)]),(3,[(1,2,4),(2,2,4)]),(4,[(1,2,4),(2,2,4)]),(3,[(1,1,6),(0,2,21)]),(12,[]),(3,[(1,2,4),(1,4,6)]),(8,[(1,2,4)]),(4,[(1,2,4),(1,4,6)]),(0,[(1,2,3),(1,11,4)]),(3,[(1,2,3),(1,11,4)]),(1,[(1,2,3),(1,11,4)]),(2,[(1,2,3),(1,11,4)]),(5,[(1,11,4)]),(4,[(1,2,3),(1,11,4)]),(2,[(1,0,6)]),(2,[(1,0,6),(3,2,30)]),(5,[(1,0,6)]),(20,[]),(11,[]),(8,[(1,3,4)]),(4,[(1,3,5)]),(4,[(2,2,6),(1,3,5)]),(0,[(1,1,6),(1,3,4)]),(3,[(1,1,6),(1,3,4)]),(3,[(1,2,4),(1,4,3)]),(2,[(1,2,4),(1,4,3)]),(5,[(1,2,4)]),(4,[(1,2,4),(1,4,3)]),(3,[(1,1,6),(1,3,6)]),(4,[(1,1,6),(1,3,6)]),(3,[(1,1,6),(3,4,21)]),(0,[(1,3,4),(1,7,5)]),(3,[(1,3,4),(1,7,5)]),(1,[(1,3,4),(1,7,5)]),(2,[(1,3,4),(1,7,5)]),(4,[(1,3,4),(1,7,5)]),(2,[(1,2,3),(2,2,6)]),(5,[(2,2,6)]),(4,[(1,2,3),(2,2,6)]),(0,[(1,3,4)]),(1,[(1,3,4)]),(5,[(1,7,5)]),(3,[(2,2,4),(2,37,6)]),(2,[(2,2,4),(2,37,6)]),(3,[(1,3,4),(3,2,7)]),(2,[(1,3,4),(3,2,7)]),(4,[(1,3,4),(3,2,7)]),(6,[(2,2,6)]),(3,[(2,2,4),(2,2,6)]),(4,[(2,2,6)]),(6,[(1,3,5)]),(4,[(2,2,4),(1,5,6)]),(4,[(1,2,6),(2,2,6)]),(2,[(1,2,6)]),(4,[(1,2,6),(1,3,5)]),(5,[(1,2,6)]),(0,[(1,4,3),(1,4,5)]),(3,[(1,4,3),(1,4,5)]),(2,[(1,4,3),(1,4,5)]),(4,[(1,4,3),(1,4,5)]),(0,[(2,2,4),(1,37,3)]),(3,[(2,2,4),(1,37,3)]),(2,[(2,2,4),(1,37,3)]),(6,[(1,37,3)]),(2,[(1,2,6),(1,3,6)]),(4,[(1,2,6),(1,3,6)]),(2,[(1,2,6),(3,4,26)]),(2,[(1,2,3),(1,2,6)]),(4,[(1,2,3),(1,2,6)]),(4,[(1,2,6),(3,5,26)]),(5,[(1,2,7)]),(3,[(1,2,3)]),(5,[(1,4,5)]),(4,[(1,2,3),(1,4,5)]),(3,[(1,3,4),(2,7,6)]),(2,[(1,3,4),(2,7,6)]),(3,[(1,3,6),(3,4,17)]),(2,[(1,3,6),(3,4,17)]),(6,[(1,3,6)]),(0,[(2,2,6),(1,31,3)]),(3,[(2,2,6),(1,31,3)]),(8,[(1,31,3)]),(2,[(2,2,6),(1,31,3)]),(3,[(1,1,6),(1,2,4)]),(4,[(1,1,6),(1,2,4)]),(2,[(1,2,4)]),(0,[(1,3,4),(1,7,6)]),(3,[(1,3,4),(1,7,6)]),(1,[(1,3,4),(1,7,6)]),(2,[(1,3,4),(1,7,6)]),(5,[(1,7,6)]),(6,[(1,7,6)]),(2,[(1,3,6)]),(1,[(1,0,6)]),(2,[(1,0,6),(2,2,4)]),(6,[(1,0,6)]),(4,[(1,0,6)]),(7,[(1,0,6)]),(3,[(1,3,5),(3,1,16)]),(4,[(1,3,5),(3,1,16)]),(7,[(3,1,16)]),(5,[(2,2,7)]),(3,[(1,3,6),(3,2,17)]),(2,[(1,3,6),(3,2,17)]),(0,[(1,4,3),(1,4,6)]),(3,[(1,4,3),(1,4,6)]),(8,[(1,4,3)]),(2,[(1,4,3),(1,4,6)]),(8,[(2,2,4)]),(3,[(2,2,4),(1,37,6)]),(2,[(2,2,4),(1,37,6)]),(3,[(1,3,4),(2,7,5)]),(2,[(1,3,4),(2,7,5)]),(4,[(1,3,4),(2,7,5)]),(5,[(2,7,5)]),(7,[(1,3,4)]),(3,[(1,2,3),(2,11,5)]),(2,[(1,2,3),(2,11,5)]),(4,[(1,2,3),(2,11,5)]),(5,[(1,1,6),(1,5,6)]),(3,[(2,2,4),(1,4,5)]),(2,[(2,2,4),(1,4,5)]),(4,[(1,3,4),(0,2,7)]),(3,[(1,3,6)]),(0,[(1,3,6)]),(4,[(1,3,6)]),(2,[(1,3,5)]),(2,[(1,3,4)]),(3,[(1,3,4)]),(4,[(1,3,4)]),(3,[(2,2,6)]),(2,[(2,2,6)]),(7,[(2,2,6)]),(3,[(1,2,6)]),(7,[(1,2,6)]),(3,[(2,2,4)]),(1,[(2,2,4)]),(4,[(2,2,4)]),(7,[(2,2,4)]),(3,[(1,5,6)]),(5,[(1,5,6)]),(2,[(1,2,3)]),(4,[(1,2,3)]),(7,[(1,2,3)])] : List PoolSpec)).map some)
def B_40_5 : BT (List (List Nat)) := BT.empty
lemma B_40_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_40 5 xs.toFinset) B_40_5 := .empty
def P_40_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_40 r_40 S_40 ps_40 [0,1,2,3,4,5,6,7]
def N_40_6 : List NodeSpec := [([10,0,1,3,4,5,6],[],[]),([14,0,1,2,3,4,5],[],[]),([15,0,1,2,16,12,6],[],[]),([19,0,1,3,4,5,6],[],[]),([0,2,4,20,5,21,17],[0],[]),([0,2,3,4,5,24,21],[],[]),([0,2,22,7,5,21,17],[1],[]),([25,0,2,4,5,21,17],[],[]),([0,1,3,22,5,26,18],[1],[]),([0,1,3,28,5,26],[2],[]),([29,1,2,4,7,5,30],[],[]),([0,1,2,16,12,6,18],[2],[]),([0,1,3,4,32,5,6],[],[]),([0,1,2,7,16,6,34],[3,4,5],[]),([0,2,3,35,4,5,21],[],[]),([36,0,2,3,4,5,21],[],[]),([37,0,2,3,12,21,33],[6,7],[]),([19,0,3,4,5,21,17],[],[]),([0,1,3,22,5,39],[1,2],[]),([0,1,11,7,5,26,40],[1],[]),([0,1,3,20,5,26,40],[0],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_40_6 : checkNodesBT W_40 g_40 F_40 P_40_6 A_40 B_40_5 6 N_40_6 = true := by decide +kernel
def B_40_6 : BT (List (List Nat)) := buildBucketsBT W_40 N_40_6
set_option maxRecDepth 500000 in
lemma B_40_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_40 6 xs.toFinset) B_40_6 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound S_40_ok) A_40_ok B_40_5_ok C_40_6
def P_40_7 : BT (Option BoundPool) := buildPoolsSubBT 9 W_40 r_40 S_40 ps_40 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68]
def N_40_7 : List NodeSpec := [([0,1,2,3,42,4,5,6],[],[]),([0,1,2,3,44,4,5,6],[],[]),([0,1,2,3,4,5,46,6],[],[]),([0,1,2,3,28,5,6],[1,2,8,9,10],[0]),([48,0,1,2,3,4,5,6],[],[]),([45,0,1,2,4,5,16,6],[11],[]),([0,1,2,49,3,4,5,6],[],[]),([0,2,3,4,5,6,51],[12,13],[]),([52,0,1,2,3,4,5,6],[],[]),([0,1,53,3,4,7,5,6],[14],[]),([19,0,1,3,4,5,6,18],[1],[]),([19,0,1,3,4,5,6],[15],[]),([0,1,53,3,4,5,6,18],[],[0]),([0,1,2,3,55,4,5,6],[],[]),([0,1,53,3,4,5,6],[1,2],[]),([0,1,2,57,3,4,5,6],[16],[]),([0,1,2,3,4,8,6,33],[0,3,17],[]),([58,0,1,2,3,4,5,6],[],[]),([0,1,2,3,5,8,6,40],[0,3],[]),([59,0,1,2,4,7,5,6],[18,19],[]),([0,1,2,3,7,12,6,33],[3,17,20],[1]),([43,0,1,2,3,4,16,6],[5],[]),([19,0,1,2,3,4,5,6],[],[]),([56,0,1,2,3,5,6,40],[3],[]),([15,0,1,2,3,5,12,6],[11],[0]),([0,1,2,3,5,12,6,18],[2],[0]),([19,0,1,3,4,7,5,6],[21],[]),([0,1,2,7,16,12,6],[2,3,17,22,23,24,25,26],[0,1]),([25,0,1,2,3,5,6,40],[0,27],[1]),([0,1,2,3,4,5,60,6],[13,28],[]),([0,1,2,3,4,5,6,61],[29],[]),([0,1,2,3,4,5,39],[1,2,30,31],[0,1]),([0,1,2,3,63,4,5,6],[32],[]),([31,50,0,2,3,4,5,6],[12],[]),([0,1,2,3,4,5,65,6],[13,28],[]),([19,0,1,3,4,5,6,17],[33],[0]),([0,1,2,3,66,7,5,6],[5],[]),([0,1,2,3,4,5,68,6],[],[]),([0,1,27,3,4,5,26],[0,1,2],[0]),([0,1,2,11,7,5,12,6],[2,3,34,35],[]),([0,1,38,3,22,5,6],[1,2,20],[0]),([50,0,2,3,4,22,5,6],[36],[]),([0,1,2,3,4,5,6,9],[13,16,37,38,39],[0]),([31,0,1,3,22,7,5,6],[20],[]),([0,2,11,4,7,5,6,21],[1],[]),([0,1,2,3,4,20,5,6],[],[]),([0,1,2,3,4,5,26,18],[1],[0,1]),([0,1,3,22,5,26,40],[0,1,18,40,41],[0]),([0,1,2,3,16,12,6,40],[3,17,42],[0]),([69,0,1,2,3,4,5,6],[13,28,38,43],[]),([0,1,2,3,4,70,5,6],[],[]),([37,0,2,3,5,12,6,21],[7,44],[0]),([0,1,2,3,4,5,71,6],[13,28],[1]),([0,1,3,4,20,5,6,26],[0],[0,1]),([0,1,2,3,7,5,6,72],[5],[]),([0,2,74,3,4,5,6,21],[],[]),([0,1,2,11,7,5,6,40],[1],[0,1]),([50,2,3,4,5,6,30],[12,45],[]),([0,1,3,22,7,5,6,26],[20],[0,1]),([31,0,1,3,4,20,5,6],[],[0]),([50,0,2,3,4,5,6,26],[12],[]),([0,2,3,22,7,5,6,21],[1],[0,1]),([50,0,2,3,4,5,6,40],[45],[]),([75,0,1,2,4,7,5,6],[18,46],[]),([0,1,2,3,4,5,76,6],[13,28,38,43],[]),([0,2,11,4,5,21,17],[13,46,47,48],[0]),([0,2,4,7,5,21,17],[17,46,47,49,50],[0]),([41,0,1,2,3,4,16,6],[3,5],[]),([0,1,3,11,4,5,26,40],[1],[0,1]),([0,1,2,3,4,5,78,6],[13,28],[]),([0,1,2,11,22,7,5,6],[1],[]),([0,2,3,4,20,5,6,21],[0],[0]),([0,2,3,4,80,5,6,21],[],[]),([81,0,1,2,3,5,12,6],[11],[]),([25,0,2,3,4,5,6,21],[],[0]),([0,1,2,3,4,5,6,82],[],[]),([0,1,27,11,4,5,6],[1,5,46],[]),([0,1,2,3,5,12,26,40],[2,3,51],[]),([29,1,2,3,4,5,30],[46,52],[0,1]),([36,0,1,2,3,4,5,6],[],[0,1]),([0,2,3,4,12,21,33],[7,17,53,54,55],[0]),([0,1,2,7,5,16,6,40],[3,17,56],[0]),([0,2,3,4,5,21,17,18],[1,46],[0]),([0,1,2,3,4,5,83,6],[13,28,38,43],[]),([84,0,1,2,4,7,5,6],[17,18],[]),([0,1,2,3,77,5,12,6],[11],[]),([15,0,1,2,3,22,5,6],[20],[]),([85,0,1,2,3,4,5,6],[],[]),([67,0,1,2,3,5,12,6],[11,57],[]),([86,2,3,4,5,6,21],[55,58,59,60],[]),([0,1,2,3,4,5,6,88],[],[]),([37,0,1,2,3,16,12,6],[2,3,17],[]),([0,1,2,3,4,16,6,34],[3,5,61],[0]),([2,90,3,4,5,6,21],[1,62,63],[]),([0,1,2,3,7,5,6,34],[3,5,64],[0]),([0,2,3,4,22,5,21,33],[1,65,66],[]),([0,2,3,4,5,21,33,34],[1,63,65,67],[]),([29,0,1,2,4,7,5,6],[18],[0]),([0,1,2,91,3,4,5,6],[],[]),([0,1,2,3,93,7,5,6],[20],[]),([0,1,2,3,22,5,6,18],[1],[0]),([0,1,2,3,20,5,6,40],[0],[0,1]),([94,0,1,2,3,4,5,6],[],[]),([0,1,2,3,4,5,6,95],[13,28],[]),([0,1,2,3,4,5,6,96],[],[0]),([0,2,3,4,22,5,21,17],[1,47,50],[0]),([0,1,2,3,4,5,97,6],[],[]),([0,1,2,3,4,5,13,6],[0,13,37,38,39],[0]),([0,1,2,3,35,4,5,6],[],[0]),([0,1,2,3,5,12,6,87],[11],[]),([37,0,2,3,4,5,21,33],[6,44,65],[0]),([37,0,1,3,5,12,6,26],[],[]),([37,50,0,2,3,4,5,6],[36],[]),([37,0,1,2,3,12,6,33],[3,55,68],[0]),([0,1,2,3,99,4,5,6],[],[]),([0,1,2,3,7,5,26,40],[20],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_40_7 : checkNodesBT W_40 g_40 F_40 P_40_7 A_40 B_40_6 7 N_40_7 = true := by decide +kernel
def B_40_7 : BT (List (List Nat)) := buildBucketsBT W_40 N_40_7
set_option maxRecDepth 500000 in
lemma B_40_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_40 7 xs.toFinset) B_40_7 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound S_40_ok) A_40_ok B_40_6_ok C_40_7
def P_40_8 : BT (Option BoundPool) := buildPoolsSubBT 9 W_40 r_40 S_40 ps_40 [0,1,2,3,5,6,7,11,12,13,16,17,18,19,20,28,29,36,37,38,39,42,43,44,46,47,50,55,57,65,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254]
def N_40_8 : List NodeSpec := [([41,0,1,2,3,4,5,6],[1,3,5,39,43,55,69,70,71,72],[0]),([0,1,2,3,4,5,6,33,47],[17,46,55,73],[1]),([43,0,1,2,3,4,5,6],[5,18,28,43,55,74,75,76],[0,1]),([84,0,1,2,3,4,5,6],[16,17,18,28,43,46,77,78,79],[0,1]),([0,1,2,3,4,5,6,17,18],[1,20,46,80],[0]),([0,1,27,2,3,4,5,6],[0,1,2,13,16,18,28,38,43,81,82],[0]),([0,1,2,3,4,5,6,47],[17,18,28,37,46,55,83,84,85,86,87],[0,1]),([0,1,2,3,4,16,6,33],[17,55,83,88,89,90,91],[0,1]),([0,1,2,3,4,16,12,6],[3,17,92,93,94,95],[0,1]),([0,1,2,3,11,4,5,6,33],[17,46,55,96],[0,1]),([37,0,2,3,4,5,6,21],[13,44,46,47,55,97,98,99,100,101],[0]),([0,1,2,3,5,12,6,40],[1,2,3,42,102,103,104,105],[0,1]),([0,1,2,3,4,5,16,6,40],[1,3,5,17,106],[0,1]),([0,1,2,3,11,4,5,6,40],[1,18,46,107],[0,1]),([81,0,1,2,3,4,5,6],[11,18,39,43,46,108,109,110,111],[0]),([0,1,2,3,4,5,6,100],[18,28,37,46,112,113,114,115,116],[0,1]),([29,0,1,2,3,4,5,6],[0,11,18,28,43,46,117,118,119],[0,1]),([37,0,1,3,4,5,6,26],[0,46,120,121,122],[0]),([0,2,3,11,4,5,6,21],[1,13,17,46,47,112,123,124,125,126],[0]),([92,0,1,2,3,4,5,6],[1,2,11,16,20,37,39,127,128,129],[]),([0,2,3,4,5,12,6,21],[7,17,105,130,131,132],[0,1]),([37,0,1,2,3,22,5,6],[1,18,46,133,134],[]),([0,89,2,3,4,5,6,21],[1,13,44,97,100,135,136],[0]),([0,1,2,3,22,5,6,40],[1,18,137,138,139],[0,1]),([0,1,2,3,4,20,5,6],[1,16,20,37,39,46,111,140,141,142,143,144,145],[0,1]),([101,1,2,3,4,5,6,30],[38,146,147,148,149,150],[1]),([0,1,2,3,4,7,5,6,26],[1,5,18,20,151],[0,1]),([31,0,1,2,3,4,5,16,6],[2,5,11,17,83,152,153],[0]),([0,2,3,4,7,5,6,21],[1,17,47,99,151,154,155],[0]),([0,1,2,3,22,7,5,6],[1,18,20,156,157,158,159],[0,1]),([31,0,1,2,3,4,7,5,6],[1,5,18,20,151],[0,1]),([0,2,3,4,5,21,17],[0,13,17,46,47,50,160,161],[0]),([73,0,2,3,4,5,6,21],[1,13,55,97,162],[0]),([0,1,2,3,4,5,8,6],[0,3,13,17,20,38,163,164,165,166,167],[0,1]),([31,0,1,3,11,4,5,6],[1,5,46,168,169,170],[0,1]),([0,1,2,3,4,7,5,8,6],[3,13,17,20,150,171,172,173],[]),([0,1,2,3,11,4,22,5,6],[1,46,111,158],[0]),([102,0,1,2,3,4,5,6],[1,2,11,16,39,43,46,174,175],[]),([25,0,1,2,3,4,5,6],[0,16,20,28,29,43,176,177,178],[0,1]),([31,37,0,1,3,4,5,6],[0,1,2,18,46,179,180,181],[]),([37,0,1,2,3,4,5,16,6],[2,5,11,17,152,182],[0]),([37,0,1,2,3,4,5,6,33],[3,11,55,68,183],[0]),([31,0,1,2,3,4,5,26],[0,1,46,184],[]),([0,1,2,3,4,5,16,6,26],[1,17,83,185,186,187],[0,1]),([0,1,2,3,7,5,12,6],[2,3,17,20,188,189,190,191],[0,1]),([0,1,2,3,77,4,5,6],[11,37,46,192,193,194,195],[0]),([0,1,2,3,4,5,26,17],[5,46,196,197],[0,1]),([67,0,1,2,3,4,5,6],[0,5,11,18,39,43,46,57,120,198],[0]),([0,1,3,11,4,5,6,26],[1,46,112,187,199,200],[0,1]),([103,0,1,2,3,4,5,6],[1,13,28,38,43,46,201],[]),([0,1,2,3,4,7,20,5,6],[1,20,46,202],[]),([0,1,2,3,11,4,5,12,6],[3,18,46,111,203,204,205],[0,1]),([0,1,2,3,11,4,20,5,6],[1,20,46,111,144],[]),([15,0,1,2,3,4,5,6],[1,11,20,28,43,151,206,207],[0,1]),([45,0,1,2,3,4,5,6],[1,11,39,43,46,208,209,210],[0]),([0,1,2,3,64,4,5,6],[1,11,28,37,46,169,211,212,213,214],[0,1]),([0,2,3,4,22,5,6,21],[1,13,47,55,99,138,215,216,217],[0,1]),([0,1,2,3,4,5,6,18],[1,11,20,37,39,46,151,218,219,220,221,222,223],[0,1]),([0,1,2,3,4,5,6,17,47],[17,46,55,224],[]),([37,1,2,3,4,5,6,30],[3,38,46,148,150,225,226,227,228,229],[]),([50,0,2,3,4,5,6],[12,13,36,230,231,232],[0]),([92,0,1,2,3,4,7,5,6],[20,233],[0,1]),([59,0,1,2,3,4,5,6],[16,18,19,28,43,46,234,235],[0,1]),([0,1,2,3,7,5,6,40],[1,18,20,107,236,237,238,239],[0,1]),([0,1,2,3,4,5,6,87],[1,11,28,43,46,240,241,242],[0]),([56,0,1,2,3,4,5,6],[0,3,5,16,17,18,20,28,43,243,244,245,246,247],[0,1]),([75,0,1,2,3,4,5,6],[5,16,18,28,43,46,248,249,250],[0,1]),([0,2,3,4,5,21,33],[0,6,17,55,65,67,251],[0]),([0,1,2,3,4,7,5,6,18],[1,20,46,151,222],[0]),([37,0,1,2,3,5,12,6],[2,3,11,18,252,253],[0]),([0,1,38,2,3,4,5,6],[0,1,2,13,16,18,20,28,38,43,254],[0,1]),([0,1,2,3,4,7,5,6,33],[3,17,20,55],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_40_8 : checkNodesBT W_40 g_40 F_40 P_40_8 A_40 B_40_7 8 N_40_8 = true := by decide +kernel
def B_40_8 : BT (List (List Nat)) := buildBucketsBT W_40 N_40_8
set_option maxRecDepth 500000 in
lemma B_40_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_40 8 xs.toFinset) B_40_8 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound S_40_ok) A_40_ok B_40_7_ok C_40_8
def P_40_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_40 r_40 S_40 ps_40 [0,1,5,11,13,17,18,20,28,39,43,46,47,55,61,68,71,73,79,83,97,99,100,101,111,121,129,151,152,169,181,182,185,187,203,210,224,247,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275]
def N_40_9 : List NodeSpec := [([0,1,2,3,4,5,6,17],[0,5,46,79,210,224,255,256,257],[0,1]),([0,1,2,3,4,5,16,6],[5,17,61,83,152,182,258],[0,1]),([0,1,2,3,4,7,5,6],[5,11,18,20,151,247,259,260,261],[0,1]),([31,0,1,2,3,4,5,6],[0,1,5,11,18,28,43,46,169,181,262,263,264],[0,1]),([0,1,2,3,4,5,6,26],[0,1,18,46,121,185,187,265,266],[0,1]),([37,0,1,2,3,4,5,6],[0,5,11,18,39,43,46,101,129,267,268,269,270],[0]),([0,1,2,3,4,5,6,33],[0,11,55,68,71,73,271,272],[0,1]),([0,1,2,3,11,4,5,6],[0,5,46,111,203,273,274,275],[0,1]),([0,2,3,4,5,6,21],[0,13,17,28,47,97,99,100],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_40_9 : checkNodesBT W_40 g_40 F_40 P_40_9 A_40 B_40_8 9 N_40_9 = true := by decide +kernel
def B_40_9 : BT (List (List Nat)) := buildBucketsBT W_40 N_40_9
set_option maxRecDepth 500000 in
lemma B_40_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_40 9 xs.toFinset) B_40_9 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound S_40_ok) A_40_ok B_40_8_ok C_40_9
def P_40_10 : BT (Option BoundPool) := buildPoolsSubBT 9 W_40 r_40 S_40 ps_40 [0,5,11,16,18,28,43]
def N_40_10 : List NodeSpec := [([0,1,2,3,4,5,6],[0,5,11,16,18,28,43],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_40_10 : checkNodesBT W_40 g_40 F_40 P_40_10 A_40 B_40_9 10 N_40_10 = true := by decide +kernel
def B_40_10 : BT (List (List Nat)) := buildBucketsBT W_40 N_40_10
set_option maxRecDepth 500000 in
lemma B_40_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_40 10 xs.toFinset) B_40_10 :=
  buildBucketsBT_sound (by decide) gp_40 W_40_ok (buildPoolsSubBT_sound S_40_ok) A_40_ok B_40_9_ok C_40_10
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_40_ok : forestRootCheck r_40 g_40 [(VAR 0,16,17),(VAR 1,8,10),(VAR 2,8,12),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,1,33),(VAR 6,4,68)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_40_in : bucketContainsBT B_40_10 r_40 = true := by decide +kernel
lemma low_40 : Lower r_40 g_40 11 := lower_of_forestBT root_40_ok B_40_10_ok root_40_in
def g_41 := 0xfffefffcfeeef000fffefffcfeeef000fffefffcfeeef000fffefffcfeeef000
def r_41 : List Nat := varsOf 63
set_option maxHeartbeats 0 in
lemma low_41 : Lower r_41 g_41 8 := by
  have hc : Lower (varsOf 62) 0xfffcfffcfcccf000fffcfffcfcccf000fffcfffcfcccf000fffcfffcfcccf000 7 := carry_of (swaps := [(0,5),(1,3),(2,3),(4,5)]) (by decide +kernel) low_9
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_42 := 0xfffffefafff0cc00fffffefafff0cc00fffffefafff0cc00fffffefafff0cc00
def r_42 : List Nat := varsOf 63
set_option maxHeartbeats 0 in
lemma low_42 : Lower r_42 g_42 8 := by
  have hc : Lower (varsOf 62) 0xfffffcf0fff0cc00fffffcf0fff0cc00fffffcf0fff0cc00fffffcf0fff0cc00 7 := carry_of (swaps := [(0,5),(1,5),(2,5)]) (by decide +kernel) low_9
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,32,33)]) (by decide +kernel) hc
def g_43 := 0xfffffeeefefafc00fffffeeefefafc00fffffeeefefafc00fffffeeefefafc00
def r_43 : List Nat := varsOf 63
def p_43 : List Nat := [10,10,11,11,12,12,13,13,14,15,17,17,19,19,20,20,21,22,22,23,25,25,26,26,28,33,33,34,34,35,37,37,38,38,39,41,41,42,44,44,48,48,50,52,56,56]
def q_43 : List Nat := [8,2,9,3,8,4,9,5,6,7,16,1,18,3,16,4,5,18,6,7,24,9,24,18,24,32,1,32,2,3,36,5,36,6,7,40,9,40,40,36,32,16,18,36,40,24]
def F_43 : Nat := fullMask 46
set_option maxHeartbeats 0 in
lemma gp_43 : goodPairs g_43 p_43 q_43 := goodPairs_of (by decide +kernel)
def W_43 : BT Decor := buildWiresBT 4 (mkBase p_43 q_43 r_43) [(0,4,5),(1,0,6),(1,4,5),(3,7,8),(3,6,8),(2,3,6),(1,3,6),(3,0,8),(2,4,5),(3,6,5)]
lemma W_43_ok : btAll (fun x => faithful p_43 q_43 x ∧ x.1 < 2^256) W_43 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_43 : List (List (Nat × Nat)) := [[],[(1,2),(4,5)]]
def A_43 : BT (List (Nat × Nat)) := btOfList 1 al_43
set_option maxHeartbeats 0 in
lemma A_43_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_43 = g_43) A_43 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_43_0 : Slice r_43 g_43 (subcubeFast 1 0) 7 := by
  have hc : Lower (varsOf 62) 0xfffffcccfcf0fc00fffffcccfcf0fc00fffffcccfcf0fc00fffffcccfcf0fc00 7 := carry_of (swaps := [(0,5),(1,5),(2,5),(3,4),(4,5)]) (by decide +kernel) low_22
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_43_1 : Slice r_43 g_43 (subcubeFast 2 0) 7 := by
  have hc : Lower (varsOf 61) 0xfffffaaafafaf000fffffaaafafaf000fffffaaafafaf000fffffaaafafaf000 7 := carry_of (swaps := [(0,1),(1,5),(2,3),(3,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_43_2 : Slice r_43 g_43 (subcubeFast 4 0) 7 := by
  have hc : Lower (varsOf 59) 0xffffeeeeeeaacc00ffffeeeeeeaacc00ffffeeeeeeaacc00ffffeeeeeeaacc00 7 := carry_of (swaps := [(0,1),(1,3),(2,5),(4,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_43_3 : Slice r_43 g_43 (identDom 1 4) 8 := by
  have hc : Lower (varsOf 47) 0xfeeefeeefcc8fcc8feeefeeefcc8fcc8feeefeeefcc8fcc8feeefeeefcc8fcc8 8 := carry_of (swaps := [(1,4),(2,4),(3,4),(4,5)]) (by decide +kernel) low_2
  exact slice_ident (u := 1) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_43_4 : Slice r_43 g_43 (identDom 2 5) 8 := by
  have hc : Lower (varsOf 31) 0xfefafce0fefafce0fefafce0fefafce0fefafce0fefafce0fefafce0fefafce0 8 := carry_of (swaps := [(2,4),(3,4)]) (by decide +kernel) low_2
  exact slice_ident (u := 2) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_43_5 : Slice r_43 g_43 (subcubeFast 8 0) 6 := by
  have hc : Lower (varsOf 55) 0xffffeeeefafa0000ffffeeeefafa0000ffffeeeefafa0000ffffeeeefafa0000 6 := carry_of (swaps := [(0,2),(1,2),(3,5),(4,5)]) (by decide +kernel) low_25
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_43_6 : Slice r_43 g_43 (subcubeFast 0 8) 6 := by
  have hc : Lower (varsOf 55) 0xfffffefefefefcfcfffffefefefefcfcfffffefefefefcfcfffffefefefefcfc 6 := carry_of (swaps := [(1,3),(2,4),(3,5),(4,5)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 0) (o := 8) (by decide +kernel) hc
def S_43 : BT (Option (Nat × Nat)) := btOfList 3 [some (subcubeFast 1 0,7),some (subcubeFast 2 0,7),some (subcubeFast 4 0,7),some (identDom 1 4,8),some (identDom 2 5,8),some (subcubeFast 8 0,6),some (subcubeFast 0 8,6)]
lemma S_43_ok : btAll (fun o => ∀ p, o = some p → Slice r_43 g_43 p.1 p.2) S_43 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_43_0) (forall_cons (fun _ h => by cases h; exact sl_43_1) (forall_cons (fun _ h => by cases h; exact sl_43_2) (forall_cons (fun _ h => by cases h; exact sl_43_3) (forall_cons (fun _ h => by cases h; exact sl_43_4) (forall_cons (fun _ h => by cases h; exact sl_43_5) (forall_cons (fun _ h => by cases h; exact sl_43_6) (fun _ h => (List.not_mem_nil h).elim))))))))
def ps_43 : BT (Option PoolSpec) := btOfList 6 ((([(3,[(0,4,5),(1,3,6),(1,4,5)]),(4,[(0,4,5),(1,3,6),(1,4,5)]),(0,[(0,4,5),(1,4,5),(3,6,8)]),(0,[(0,4,5),(1,4,5)]),(3,[(0,4,5),(1,4,5),(3,6,8)]),(1,[(0,4,5),(1,4,5),(3,6,8)]),(4,[(0,4,5),(1,4,5),(3,6,8)]),(2,[(0,4,5),(1,4,5),(3,6,8)]),(3,[(0,4,5),(1,0,6),(1,4,5)]),(1,[(0,4,5),(1,0,6),(1,4,5)]),(4,[(0,4,5),(1,0,6),(1,4,5)]),(2,[(0,4,5),(1,0,6),(1,4,5)]),(3,[(0,4,5),(1,0,6)]),(1,[(0,4,5),(1,0,6)]),(4,[(0,4,5),(1,0,6)]),(2,[(0,4,5),(1,0,6)]),(0,[]),(6,[]),(0,[(0,4,5),(2,3,6)]),(3,[(0,4,5),(2,3,6)]),(1,[(0,4,5),(2,3,6)]),(4,[(0,4,5),(2,3,6)]),(2,[(0,4,5),(2,3,6)]),(0,[(0,4,5),(1,3,6)]),(3,[(0,4,5),(1,3,6)]),(1,[(0,4,5),(1,3,6)]),(4,[(0,4,5),(1,3,6)]),(2,[(0,4,5),(1,3,6)]),(5,[]),(3,[(0,4,5),(3,6,4)]),(3,[(0,4,5),(1,4,5)]),(1,[(0,4,5),(1,4,5)]),(4,[(0,4,5),(1,4,5)]),(2,[(0,4,5),(1,4,5)]),(4,[(1,4,5)]),(3,[]),(1,[]),(4,[]),(2,[]),(0,[(2,4,5)]),(1,[(2,4,5)]),(2,[(2,4,5)]),(0,[(1,4,5)]),(1,[(1,4,5)]),(2,[(1,4,5)]),(0,[(0,4,5)]),(3,[(0,4,5)]),(1,[(0,4,5)]),(4,[(0,4,5)]),(2,[(0,4,5)])] : List PoolSpec)).map some)
def B_43_3 : BT (List (List Nat)) := BT.empty
lemma B_43_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_43 3 xs.toFinset) B_43_3 := .empty
def P_43_4 : BT (Option BoundPool) := buildPoolsSubBT 6 W_43 r_43 S_43 ps_43 []
def N_43_4 : List NodeSpec := [([9,10,1,2,3],[],[]),([10,0,1,2,3],[],[]),([11,10,0,1,2],[],[]),([10,0,1,2,12],[],[]),([10,1,2,3,7],[],[]),([11,1,2,7,8],[],[]),([1,2,7,12,8],[],[]),([1,2,3,7,8],[],[]),([10,13,1,2,3],[],[]),([9,1,2,3,8],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_43_4 : checkNodesBT W_43 g_43 F_43 P_43_4 A_43 B_43_3 4 N_43_4 = true := by decide +kernel
def B_43_4 : BT (List (List Nat)) := buildBucketsBT W_43 N_43_4
set_option maxRecDepth 500000 in
lemma B_43_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_43 4 xs.toFinset) B_43_4 :=
  buildBucketsBT_sound (by decide) gp_43 W_43_ok (buildPoolsSubBT_sound S_43_ok) A_43_ok B_43_3_ok C_43_4
def P_43_5 : BT (Option BoundPool) := buildPoolsSubBT 6 W_43 r_43 S_43 ps_43 [0,1,2,3,4,5,6,7,8,9,10,11]
def N_43_5 : List NodeSpec := [([13,1,2,3,4,5],[],[]),([0,1,2,6,12,8],[0,1],[0]),([1,2,3,4,7,8],[],[]),([10,0,1,2,3],[2],[0]),([1,2,3,4,7,5],[],[0]),([1,2,3,7,8],[3],[0]),([14,1,2,3,7,5],[],[0]),([1,2,4,7,12,5],[],[0]),([10,0,1,2,3,4],[],[]),([13,1,2,3,6,8],[],[0]),([14,10,0,1,2,3],[],[]),([11,1,2,4,7,5],[],[0]),([10,0,1,2,3,6],[2,4,5,6,7],[0]),([1,2,3,6,7,8],[8,9,10,11],[0]),([10,0,1,2,3,8],[2],[0]),([11,0,1,2,6,8],[],[0]),([0,1,2,3,6,8],[],[0]),([14,15,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_43_5 : checkNodesBT W_43 g_43 F_43 P_43_5 A_43 B_43_4 5 N_43_5 = true := by decide +kernel
def B_43_5 : BT (List (List Nat)) := buildBucketsBT W_43 N_43_5
set_option maxRecDepth 500000 in
lemma B_43_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_43 5 xs.toFinset) B_43_5 :=
  buildBucketsBT_sound (by decide) gp_43 W_43_ok (buildPoolsSubBT_sound S_43_ok) A_43_ok B_43_4_ok C_43_5
def P_43_6 : BT (Option BoundPool) := buildPoolsSubBT 6 W_43 r_43 S_43 ps_43 [3,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
def N_43_6 : List NodeSpec := [([14,15,0,1,2,3,4],[],[0]),([14,15,0,1,2,3],[],[0,1]),([1,2,3,4,7,5],[],[0,1]),([1,2,3,6,4,7,5],[12,13,14,15,16],[0,1]),([11,0,1,2,6,4,5],[17,18,19,20,21,22],[0]),([0,1,2,6,4,12,5],[23,24,25,26,27,28],[0]),([13,1,2,3,4,5,8],[16],[0]),([0,1,2,3,4,5,8],[16],[0]),([13,1,2,3,4,5],[],[]),([14,0,1,2,3,6,5],[16,29],[0]),([14,0,1,2,3,4,5],[],[0]),([0,1,2,3,6,8],[3,30,31,32,33],[0]),([0,1,2,3,6,4,8],[34],[0]),([0,1,2,3,6,4,5],[16,17,28,35,36,37,38],[0]),([14,0,1,2,3,4,8],[16],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_43_6 : checkNodesBT W_43 g_43 F_43 P_43_6 A_43 B_43_5 6 N_43_6 = true := by decide +kernel
def B_43_6 : BT (List (List Nat)) := buildBucketsBT W_43 N_43_6
set_option maxRecDepth 500000 in
lemma B_43_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_43 6 xs.toFinset) B_43_6 :=
  buildBucketsBT_sound (by decide) gp_43 W_43_ok (buildPoolsSubBT_sound S_43_ok) A_43_ok B_43_5_ok C_43_6
def P_43_7 : BT (Option BoundPool) := buildPoolsSubBT 6 W_43 r_43 S_43 ps_43 [16,17,28,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49]
def N_43_7 : List NodeSpec := [([14,0,1,2,3,4,5],[16,17,28,36,38,39,40,41],[0,1]),([0,1,2,3,4,5,8],[17,28,42,43,44],[0,1]),([0,1,2,3,6,4,5],[16,17,28,35,36,37,38,45,46,47,48,49],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_43_7 : checkNodesBT W_43 g_43 F_43 P_43_7 A_43 B_43_6 7 N_43_7 = true := by decide +kernel
def B_43_7 : BT (List (List Nat)) := buildBucketsBT W_43 N_43_7
set_option maxRecDepth 500000 in
lemma B_43_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_43 7 xs.toFinset) B_43_7 :=
  buildBucketsBT_sound (by decide) gp_43 W_43_ok (buildPoolsSubBT_sound S_43_ok) A_43_ok B_43_6_ok C_43_7
def P_43_8 : BT (Option BoundPool) := buildPoolsSubBT 6 W_43 r_43 S_43 ps_43 [16,17,28,36,38]
def N_43_8 : List NodeSpec := [([0,1,2,3,4,5],[16,17,28,36,38],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_43_8 : checkNodesBT W_43 g_43 F_43 P_43_8 A_43 B_43_7 8 N_43_8 = true := by decide +kernel
def B_43_8 : BT (List (List Nat)) := buildBucketsBT W_43 N_43_8
set_option maxRecDepth 500000 in
lemma B_43_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_43 8 xs.toFinset) B_43_8 :=
  buildBucketsBT_sound (by decide) gp_43 W_43_ok (buildPoolsSubBT_sound S_43_ok) A_43_ok B_43_7_ok C_43_8
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_43_ok : forestRootCheck r_43 g_43 [(VAR 0,16,17),(VAR 1,8,10),(VAR 2,8,12),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,1,33)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_43_in : bucketContainsBT B_43_8 r_43 = true := by decide +kernel
lemma low_43 : Lower r_43 g_43 9 := lower_of_forestBT root_43_ok B_43_8_ok root_43_in
def g_44 := 0xffffffffffeefeeefffefafaffccf000ffffffffffeefeeefffefafaffccf000
def r_44 : List Nat := varsOf 127
def p_44 : List Nat := [12,12,13,13,14,14,15,15,18,18,19,19,22,22,23,23,24,24,25,25,26,27,28,29,33,33,35,35,36,36,37,38,38,39,41,41,43,43,44,46,49,49,50,50,52,52,53,56,56,58,65,65,66,66,67,69,69,70,70,71,73,73,74,74,75,76,76,81,81,82,85,85,86,88,88,92,96,96,98,100,104,104,106,112,112,116]
def q_44 : List Nat := [8,4,9,5,10,6,11,7,16,2,17,3,20,6,21,7,16,8,17,9,10,11,20,21,32,1,34,3,32,4,5,34,6,7,40,9,42,11,40,42,48,17,48,34,48,20,21,48,40,42,64,1,64,2,3,68,5,68,6,7,72,9,72,10,11,72,68,80,17,80,84,21,84,80,72,84,64,32,34,68,72,40,42,80,48,84]
def F_44 : Nat := fullMask 86
set_option maxHeartbeats 0 in
lemma gp_44 : goodPairs g_44 p_44 q_44 := goodPairs_of (by decide +kernel)
def W_44 : BT Decor := buildWiresBT 8 (mkBase p_44 q_44 r_44) [(0,5,6),(1,5,6),(3,7,8),(3,5,6),(1,10,3),(0,0,8),(1,3,8),(3,12,13),(1,9,3),(3,7,13),(1,1,5),(2,17,6),(1,17,6),(3,12,19),(3,2,13),(1,0,5),(1,22,6),(3,0,23),(1,0,2),(2,25,6),(3,0,6),(1,2,4),(1,0,6),(0,22,29),(3,30,8),(1,4,7),(1,3,4),(1,2,5),(1,2,6),(0,34,35),(0,5,35),(1,0,37),(3,0,5),(0,39,6),(3,40,8),(0,9,0),(1,1,3),(2,43,4),(2,3,7),(0,25,5),(1,46,6),(1,3,5),(3,2,48),(1,4,5),(0,17,35),(2,1,7),(1,3,7),(0,30,8),(1,24,3),(3,2,55),(3,1,6),(1,57,5),(3,0,58),(2,0,7),(1,24,1),(2,5,6),(1,3,6),(3,5,63),(2,50,6),(0,50,6),(1,2,66),(1,4,6),(3,1,68),(1,1,7),(3,1,5),(0,71,6),(1,72,2),(0,5,29),(1,2,74),(1,0,1),(0,22,6),(1,2,77),(1,27,1),(0,25,6),(1,0,4),(0,81,6),(1,2,82),(0,76,6),(3,46,6),(3,2,6),(0,86,5),(1,87,0),(3,39,6),(1,76,5),(2,90,6),(2,22,6),(1,25,6),(0,93,5),(3,27,50),(2,76,6),(1,84,2),(1,40,2),(3,71,6),(1,27,5),(3,7,50),(3,0,17),(3,2,5),(1,103,0),(1,103,6),(0,17,6),(1,2,106),(0,34,6),(3,1,35),(1,109,5),(3,0,19),(1,62,4),(1,10,1),(1,62,1),(1,62,0),(3,2,8),(1,1,6),(3,27,5),(1,0,3),(2,119,6),(3,0,48),(3,0,34),(1,86,1),(1,39,1),(0,119,5),(3,25,5),(3,25,6),(0,76,5),(3,2,29),(2,81,6),(3,2,117),(1,39,4),(3,29,5),(3,2,22),(2,34,6),(2,76,2),(3,57,5),(3,4,6),(1,138,0),(3,2,17),(1,138,5),(1,25,5),(1,103,1),(0,63,5),(3,35,5),(2,48,6),(1,86,0),(1,86,5),(2,71,6),(0,117,5),(3,0,50)]
lemma W_44_ok : btAll (fun x => faithful p_44 q_44 x ∧ x.1 < 2^256) W_44 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_44 : List (List (Nat × Nat)) := [[],[(1,2),(3,4),(5,6)]]
def A_44 : BT (List (Nat × Nat)) := btOfList 1 al_44
set_option maxHeartbeats 0 in
lemma A_44_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_44 = g_44) A_44 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_44_0 : Slice r_44 g_44 (identDom 1 2) 10 := by
  have hc : Lower (varsOf 123) 0xffffffffffeeeeeeffeeeeeeffcccc00ffffffffffeeeeeeffeeeeeeffcccc00 10 := carry_of (swaps := [(0,2),(1,5),(2,6),(3,6),(4,5),(5,6)]) (by decide +kernel) low_10
  exact slice_ident (u := 1) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_1 : Slice r_44 g_44 (identDom 3 6) 9 := by
  have hc : Lower (varsOf 63) 0xfffefffaffccfe00fffefffaffccfe00fffefffaffccfe00fffefffaffccfe00 9 := carry_of (swaps := [(1,2),(3,5),(4,5)]) (by decide +kernel) low_14
  exact slice_ident (u := 3) (v := 6) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_2 : Slice r_44 g_44 (identDom 4 5) 9 := by
  have hc : Lower (varsOf 95) 0xfffffeeefffffeeefffef000fffef000fffffeeefffffeeefffef000fffef000 9 := carry_of (swaps := [(4,5),(5,6)]) (by decide +kernel) low_14
  exact slice_ident (u := 4) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_3 : Slice r_44 g_44 (subcubeFast 2 0) 8 := by
  have hc : Lower (varsOf 125) 0xffffffffffaafaaafffafafaff00f000ffffffffffaafaaafffafafaff00f000 8 := carry_of (swaps := [(0,2),(1,6),(2,6),(3,4),(4,6)]) (by decide +kernel) low_41
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_4 : Slice r_44 g_44 (subcubeFast 4 0) 8 := by
  have hc : Lower (varsOf 123) 0xffffffffffeeeeeeffeeaaaaffcc0000ffffffffffeeeeeeffeeaaaaffcc0000 8 := carry_of (swaps := [(0,2),(2,6),(3,6),(5,6)]) (by decide +kernel) low_41
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_5 : Slice r_44 g_44 (subcubeFast 8 0) 8 := by
  have hc : Lower (varsOf 119) 0xffffffffeeeeeeeefefefafacccc0000ffffffffeeeeeeeefefefafacccc0000 8 := carry_of (swaps := [(0,2),(1,3),(3,6),(4,6)]) (by decide +kernel) low_42
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_6 : Slice r_44 g_44 (subcubeFast 16 0) 8 := by
  have hc : Lower (varsOf 111) 0xfffffffffeeefeeefafafafaf000f000fffffffffeeefeeefafafafaf000f000 8 := carry_of (swaps := [(0,2),(1,2),(2,3),(4,6),(5,6)]) (by decide +kernel) low_42
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_7 : Slice r_44 g_44 (subcubeFast 1 0) 8 := by
  have hc : Lower (varsOf 126) 0xffffffffffccfcccfffcf0f0ffccf000ffffffffffccfcccfffcf0f0ffccf000 8 := carry_of (swaps := [(0,6),(1,6),(2,3),(3,6),(4,5),(5,6)]) (by decide +kernel) low_39
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_8 : Slice r_44 g_44 (subcubeFast 12 0) 7 := by
  have hc : Lower (varsOf 115) 0xffffffffeeeeeeeeeeeeaaaacccc0000ffffffffeeeeeeeeeeeeaaaacccc0000 7 := carry_of (swaps := [(0,1),(1,3),(2,5),(3,6),(4,6)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 12) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_9 : Slice r_44 g_44 (subcubeFast 18 0) 7 := by
  have hc : Lower (varsOf 109) 0xfffffffffaaafaaafafafafaf000f000fffffffffaaafaaafafafafaf000f000 7 := carry_of (swaps := [(0,1),(1,5),(2,3),(3,5),(4,6),(5,6)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 18) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_10 : Slice r_44 g_44 (identDom 0 1) 9 := by
  have hc : Lower (varsOf 125) 0xffffffffffaafaaafffafafaffaaf000ffffffffffaafaaafffafafaffaaf000 9 := carry_of (swaps := [(0,4),(1,6),(2,6),(4,6)]) (by decide +kernel) low_43
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_11 : Slice r_44 g_44 (identDom 0 2) 9 := by
  have hc : Lower (varsOf 123) 0xffffffffffeeeeeeffeeaaaaffccaa00ffffffffffeeeeeeffeeaaaaffccaa00 9 := carry_of (swaps := [(0,4),(2,6),(3,6),(4,6),(5,6)]) (by decide +kernel) low_43
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_12 : Slice r_44 g_44 (identDom 0 4) 9 := by
  have hc : Lower (varsOf 111) 0xfffffffffeeefeeefafafafafa88fa88fffffffffeeefeeefafafafafa88fa88 9 := carry_of (swaps := [(0,5),(1,5),(2,3),(3,5),(4,6)]) (by decide +kernel) low_20
  exact slice_ident (u := 0) (v := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_13 : Slice r_44 g_44 (identDom 0 3) 9 := by
  have hc : Lower (varsOf 119) 0xffffffffeeeeeeeefefefafaeeeea0a0ffffffffeeeeeeeefefefafaeeeea0a0 9 := carry_of (swaps := [(0,5),(1,3),(2,5),(3,6),(4,6),(5,6)]) (by decide +kernel) low_20
  exact slice_ident (u := 0) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_14 : Slice r_44 g_44 (subcubeFast 4 16) 6 := by
  have hc : Lower (varsOf 107) 0xffffffffffeeffeeffeeffeeffccffccffffffffffeeffeeffeeffeeffccffcc 6 := carry_of (swaps := [(1,3),(2,5),(3,4),(4,6),(5,6)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 4) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_15 : Slice r_44 g_44 (subcubeFast 16 8) 6 := by
  have hc : Lower (varsOf 103) 0xfffffffffefefefefafafafaf0f0f0f0fffffffffefefefefafafafaf0f0f0f0 6 := carry_of (swaps := [(0,1),(2,4),(3,5),(4,6),(5,6)]) (by decide +kernel) low_31
  exact slice_fast_direct_f (z := 16) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_16 : Slice r_44 g_44 (subcubeFast 8 16) 6 := by
  have hc : Lower (varsOf 103) 0xffffffffeeeeeeeefefefefeccccccccffffffffeeeeeeeefefefefecccccccc 6 := carry_of (swaps := [(0,1),(1,4),(2,4),(3,5),(4,6)]) (by decide +kernel) low_31
  exact slice_fast_direct_f (z := 8) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_17 : Slice r_44 g_44 (subcubeFast 24 0) 6 := by
  have hc : Lower (varsOf 103) 0xffffffffeeeeeeeefafafafa00000000ffffffffeeeeeeeefafafafa00000000 6 := carry_of (swaps := [(0,2),(1,2),(3,5),(4,6)]) (by decide +kernel) low_25
  exact slice_fast_direct_f (z := 24) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_18 : Slice r_44 g_44 (subcubeFast 4 8) 6 := by
  have hc : Lower (varsOf 115) 0xffffffffffffeeeeffffaaaaffff0000ffffffffffffeeeeffffaaaaffff0000 6 := carry_of (swaps := [(0,1),(2,5),(3,6)]) (by decide +kernel) low_31
  exact slice_fast_direct_f (z := 4) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_19 : Slice r_44 g_44 (subcubeFast 2 16) 6 := by
  have hc : Lower (varsOf 109) 0xffffffffffaaffaafffafffaff00ff00ffffffffffaaffaafffafffaff00ff00 6 := carry_of (swaps := [(0,1),(1,5),(2,5),(3,4),(4,6),(5,6)]) (by decide +kernel) low_31
  exact slice_fast_direct_f (z := 2) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_20 : Slice r_44 g_44 (subcubeFast 2 8) 6 := by
  have hc : Lower (varsOf 117) 0xfffffffffffffafafffffafafffff0f0fffffffffffffafafffffafafffff0f0 6 := carry_of (swaps := [(1,5),(2,3),(3,6)]) (by decide +kernel) low_17
  exact slice_fast_direct_f (z := 2) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_21 : Slice r_44 g_44 (subcubeFast 20 8) 5 := by
  have hc : Lower (varsOf 99) 0xffffffffeeeeeeeeaaaaaaaa00000000ffffffffeeeeeeeeaaaaaaaa00000000 5 := carry_of (swaps := [(0,1),(2,4),(3,5),(4,6),(5,6)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 20) (o := 8) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_22 : Slice r_44 g_44 (subcubeFast 10 16) 5 := by
  have hc : Lower (varsOf 101) 0xffffffffaaaaaaaafafafafa00000000ffffffffaaaaaaaafafafafa00000000 5 := carry_of (swaps := [(0,1),(1,4),(2,4),(3,5),(4,6)]) (by decide +kernel) low_1
  exact slice_fast_direct_f (z := 10) (o := 16) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_23 : Slice r_44 g_44 (subcubeFast 96 1) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 96) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_24 : Slice r_44 g_44 (subcubeFast 82 0) 4 := by
  have hc : Lower (varsOf 45) 0xfafafafaf000f000fafafafaf000f000fafafafaf000f000fafafafaf000f000 4 := carry_of (swaps := [(1,4),(3,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 82) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_25 : Slice r_44 g_44 (subcubeFast 80 2) 4 := by
  have hc : Lower (varsOf 45) 0xfafafafaf000f000fafafafaf000f000fafafafaf000f000fafafafaf000f000 4 := carry_of (swaps := [(1,4),(3,4),(4,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 80) (o := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_26 : Slice r_44 g_44 (subcubeFast 97 0) 4 := by
  have hc : Lower (varsOf 30) 0xffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000ffccf000 4 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 97) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_27 : Slice r_44 g_44 (subcubeFast 37 0) 4 := by
  have hc : Lower (varsOf 90) 0xffccccccffccccccffcc0000ffcc0000ffccccccffccccccffcc0000ffcc0000 4 := carry_of (swaps := [(0,4),(1,2),(2,5),(3,4),(5,6)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 37) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_28 : Slice r_44 g_44 (subcubeFast 44 0) 4 := by
  have hc : Lower (varsOf 83) 0xeeeeeeeeeeeeeeeecccc0000cccc0000eeeeeeeeeeeeeeeecccc0000cccc0000 4 := carry_of (swaps := [(1,2),(2,4),(3,5),(5,6)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 44) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_29 : Slice r_44 g_44 (subcubeFast 40 4) 4 := by
  have hc : Lower (varsOf 83) 0xeeeeeeeeeeeeeeeecccc0000cccc0000eeeeeeeeeeeeeeeecccc0000cccc0000 4 := carry_of (swaps := [(1,2),(2,4),(3,5),(5,6)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 40) (o := 4) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_44_30 : Slice r_44 g_44 (subcubeFast 67 0) 4 := by
  have hc : Lower (varsOf 60) 0xfff0f0f0ff00f000fff0f0f0ff00f000fff0f0f0ff00f000fff0f0f0ff00f000 4 := carry_of (swaps := [(0,4),(1,5)]) (by decide +kernel) low_7
  exact slice_fast_direct_f (z := 67) (o := 0) (by decide +kernel) hc
def S_44 : BT (Option (Nat × Nat)) := btOfList 5 [some (identDom 1 2,10),some (identDom 3 6,9),some (identDom 4 5,9),some (subcubeFast 2 0,8),some (subcubeFast 4 0,8),some (subcubeFast 8 0,8),some (subcubeFast 16 0,8),some (subcubeFast 1 0,8),some (subcubeFast 12 0,7),some (subcubeFast 18 0,7),some (identDom 0 1,9),some (identDom 0 2,9),some (identDom 0 4,9),some (identDom 0 3,9),some (subcubeFast 4 16,6),some (subcubeFast 16 8,6),some (subcubeFast 8 16,6),some (subcubeFast 24 0,6),some (subcubeFast 4 8,6),some (subcubeFast 2 16,6),some (subcubeFast 2 8,6),some (subcubeFast 20 8,5),some (subcubeFast 10 16,5),some (subcubeFast 96 1,4),some (subcubeFast 82 0,4),some (subcubeFast 80 2,4),some (subcubeFast 97 0,4),some (subcubeFast 37 0,4),some (subcubeFast 44 0,4),some (subcubeFast 40 4,4),some (subcubeFast 67 0,4)]
lemma S_44_ok : btAll (fun o => ∀ p, o = some p → Slice r_44 g_44 p.1 p.2) S_44 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_44_0) (forall_cons (fun _ h => by cases h; exact sl_44_1) (forall_cons (fun _ h => by cases h; exact sl_44_2) (forall_cons (fun _ h => by cases h; exact sl_44_3) (forall_cons (fun _ h => by cases h; exact sl_44_4) (forall_cons (fun _ h => by cases h; exact sl_44_5) (forall_cons (fun _ h => by cases h; exact sl_44_6) (forall_cons (fun _ h => by cases h; exact sl_44_7) (forall_cons (fun _ h => by cases h; exact sl_44_8) (forall_cons (fun _ h => by cases h; exact sl_44_9) (forall_cons (fun _ h => by cases h; exact sl_44_10) (forall_cons (fun _ h => by cases h; exact sl_44_11) (forall_cons (fun _ h => by cases h; exact sl_44_12) (forall_cons (fun _ h => by cases h; exact sl_44_13) (forall_cons (fun _ h => by cases h; exact sl_44_14) (forall_cons (fun _ h => by cases h; exact sl_44_15) (forall_cons (fun _ h => by cases h; exact sl_44_16) (forall_cons (fun _ h => by cases h; exact sl_44_17) (forall_cons (fun _ h => by cases h; exact sl_44_18) (forall_cons (fun _ h => by cases h; exact sl_44_19) (forall_cons (fun _ h => by cases h; exact sl_44_20) (forall_cons (fun _ h => by cases h; exact sl_44_21) (forall_cons (fun _ h => by cases h; exact sl_44_22) (forall_cons (fun _ h => by cases h; exact sl_44_23) (forall_cons (fun _ h => by cases h; exact sl_44_24) (forall_cons (fun _ h => by cases h; exact sl_44_25) (forall_cons (fun _ h => by cases h; exact sl_44_26) (forall_cons (fun _ h => by cases h; exact sl_44_27) (forall_cons (fun _ h => by cases h; exact sl_44_28) (forall_cons (fun _ h => by cases h; exact sl_44_29) (forall_cons (fun _ h => by cases h; exact sl_44_30) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))
def ps_44 : BT (Option PoolSpec) := btOfList 9 ((([(5,[(0,5,6),(1,5,6),(3,7,8)]),(7,[(0,5,6),(1,5,6),(3,7,8)]),(23,[]),(4,[(0,5,6),(1,5,6),(3,7,8)]),(29,[]),(5,[(1,0,2),(3,0,6),(2,25,6)]),(5,[(0,5,6),(1,0,7),(1,5,6)]),(4,[(1,6,5),(0,5,35),(1,0,37)]),(5,[(1,2,6),(1,6,5),(0,5,35),(1,0,37)]),(7,[(0,39,6),(1,5,6),(3,40,8)]),(26,[]),(4,[(1,0,5),(0,25,5),(1,46,6)]),(5,[(1,0,2),(1,0,5),(0,25,5),(1,46,6)]),(7,[(1,5,6),(0,22,29)]),(0,[(1,0,2),(0,25,5),(1,46,6),(1,1,5)]),(4,[(0,5,6),(1,0,7),(1,5,6)]),(0,[(1,1,5),(1,2,6),(1,5,6),(0,17,35)]),(6,[(3,1,6),(1,57,5),(3,0,58)]),(13,[]),(4,[(1,5,6),(3,0,8)]),(5,[(1,5,6),(3,0,8)]),(3,[(1,5,6),(3,0,8)]),(25,[]),(3,[(0,5,6),(1,5,6),(3,7,8)]),(27,[]),(28,[]),(24,[]),(1,[(2,6,5),(3,6,5)]),(7,[(0,5,6),(1,5,6)]),(4,[(0,5,6),(1,5,6)]),(0,[(0,6,5),(1,2,7),(1,5,6)]),(3,[(0,5,6),(1,0,7),(1,5,6)]),(0,[(0,5,6),(1,0,7),(1,5,6)]),(8,[(0,5,6),(1,0,7),(1,5,6)]),(1,[(3,6,5),(3,5,63)]),(2,[(1,5,6),(3,0,8)]),(14,[]),(6,[(0,50,6),(1,2,66)]),(2,[(0,5,6),(1,2,7)]),(5,[(0,5,6),(1,5,6)]),(5,[(0,6,5),(1,2,7)]),(5,[(0,5,6),(1,0,7)]),(10,[]),(3,[(1,57,5),(3,0,58)]),(7,[(0,29,5),(1,2,74)]),(3,[]),(22,[]),(6,[(1,0,1),(3,0,5)]),(1,[(0,5,6),(1,5,6)]),(3,[(0,5,6),(1,5,6)]),(7,[]),(7,[(1,1,3),(2,43,4)]),(4,[(1,6,5),(0,5,35)]),(5,[(1,2,6),(1,6,5),(0,5,35)]),(1,[(0,6,5),(1,2,7)]),(6,[(0,81,6),(1,2,82)]),(7,[(1,6,5),(0,5,29)]),(7,[(0,76,6)]),(3,[(1,0,6),(0,76,6)]),(2,[(0,5,6),(1,0,7)]),(7,[(1,3,5),(3,2,48)]),(4,[]),(6,[]),(5,[(1,0,2),(2,25,6)]),(0,[(2,5,6),(3,5,6),(1,62,10)]),(7,[(2,5,6),(3,5,6),(1,62,10)]),(3,[(2,5,6),(3,5,6),(1,62,10)]),(3,[(1,0,5),(2,22,6)]),(0,[(1,0,2),(1,25,6),(0,93,5)]),(7,[(1,25,6),(0,93,5)]),(4,[(1,25,6),(0,93,5)]),(5,[(1,0,2),(1,25,6),(0,93,5)]),(3,[(0,76,6),(1,84,2)]),(0,[(1,0,1),(0,76,6),(1,2,6)]),(1,[(1,2,6)]),(4,[(1,5,6),(0,0,8)]),(4,[(0,35,5),(1,0,37)]),(5,[(1,2,6),(0,35,5),(1,0,37)]),(7,[(1,2,6),(0,35,5)]),(0,[(1,1,5),(1,2,6),(0,17,35)]),(2,[(0,5,6),(3,7,50)]),(6,[(1,1,5),(3,0,17)]),(5,[(3,2,5),(1,103,0)]),(5,[(3,2,5),(1,103,6)]),(3,[(0,17,6),(1,2,106)]),(6,[(1,5,6),(3,0,8)]),(0,[(1,0,2),(0,25,5),(1,46,6)]),(7,[(0,25,5),(1,46,6)]),(4,[(0,25,5),(1,46,6)]),(5,[(1,0,2),(0,25,5),(1,46,6)]),(4,[(3,0,6),(2,25,6)]),(4,[(1,6,5),(0,0,8)]),(0,[(1,1,5),(1,2,6),(1,5,6)]),(4,[(1,6,5),(3,0,8)]),(7,[(1,1,5),(2,17,6)]),(5,[(2,5,6),(3,5,6)]),(0,[(1,0,2),(1,2,5),(0,25,5)]),(7,[(1,2,5),(0,25,5)]),(4,[(0,25,5)]),(3,[(2,5,6),(3,5,6)]),(1,[]),(5,[]),(2,[]),(2,[(2,5,6)]),(3,[(2,6,5)]),(0,[]),(3,[(2,5,6)]),(0,[(2,5,6),(1,62,1)]),(15,[]),(7,[(2,5,6)]),(7,[(1,5,6)]),(4,[(1,5,6)]),(4,[(1,6,5)]),(8,[(1,6,5)]),(1,[(1,5,6),(3,0,8)]),(0,[(1,5,6),(3,0,8)]),(9,[(1,5,6),(3,0,8)]),(8,[(1,5,6),(3,0,8)]),(3,[(1,5,6),(0,0,8)]),(1,[(1,5,6),(0,0,8)]),(2,[(1,5,6),(0,0,8)]),(0,[(0,5,6),(1,5,6)]),(8,[(0,5,6),(1,5,6)]),(21,[]),(9,[(1,2,6)]),(5,[(1,2,6)]),(3,[(1,0,6)]),(6,[(1,0,6)]),(7,[(1,1,5)]),(7,[(1,1,6)]),(11,[(1,2,5)]),(8,[]),(7,[(3,27,5)]),(7,[(1,4,6)]),(3,[(1,0,5)]),(2,[(1,4,6)]),(6,[(1,0,5)]),(0,[(0,5,6),(3,7,5)]),(7,[(2,22,6)]),(5,[(2,119,6)]),(20,[]),(8,[(2,119,6)]),(7,[(1,3,5)]),(5,[(1,5,6)]),(7,[(0,29,5)]),(3,[(3,0,17)]),(9,[(3,0,17)]),(3,[(3,71,6)]),(9,[(3,71,6)]),(8,[(3,0,48)]),(4,[(3,0,34)]),(8,[(3,0,34)]),(7,[(1,2,5)]),(0,[(1,0,1),(1,76,5)]),(7,[(1,76,5)]),(3,[(1,76,5)]),(0,[(1,0,2),(1,2,4)]),(7,[(1,2,4)]),(9,[(1,0,2)]),(0,[(3,2,6),(1,86,1)]),(3,[(3,2,6)]),(8,[(1,86,1)]),(2,[(3,0,5)]),(12,[]),(7,[(1,4,5)]),(7,[(1,3,4)]),(5,[(1,0,5)]),(17,[]),(4,[(1,0,5)]),(7,[(1,39,1)]),(3,[(3,0,5)]),(0,[(3,0,5),(1,39,1)]),(0,[(1,0,2),(1,2,5)]),(4,[(2,25,6)]),(7,[(2,25,6)]),(8,[(2,25,6)]),(30,[]),(2,[(1,0,1)]),(5,[(0,119,5)]),(7,[(0,119,5)]),(8,[(0,119,5)]),(7,[(1,2,6)]),(4,[(3,25,5)]),(8,[(3,25,5)]),(7,[(3,25,5)]),(0,[(1,0,2),(1,2,6)]),(4,[(3,25,6)]),(3,[(2,76,6)]),(9,[(2,76,6)]),(3,[(1,57,5)]),(6,[(3,1,6),(1,57,5)]),(9,[(1,57,5)]),(3,[(0,76,5)]),(7,[(0,76,5)]),(4,[(1,0,6)]),(7,[(3,2,29)]),(8,[(1,0,6)]),(3,[(3,6,5)]),(6,[(3,6,5)]),(3,[(1,2,6)]),(0,[(1,0,1),(1,2,6)]),(3,[(0,5,6),(1,0,7)]),(7,[(0,5,6)]),(3,[(2,43,4)]),(5,[(2,43,4)]),(6,[(2,81,6)]),(9,[(2,81,6)]),(0,[(1,1,6),(3,2,117)]),(8,[(1,1,6)]),(9,[(3,2,117)]),(7,[(1,27,5)]),(3,[(0,5,6)]),(7,[(0,5,6),(1,1,7)]),(0,[(0,5,6),(1,1,7)]),(11,[(1,0,5)]),(10,[(3,0,5)]),(7,[(1,1,3)]),(6,[(3,0,5)]),(7,[(1,39,4)]),(7,[(3,2,22)]),(8,[(1,0,5)]),(7,[(1,3,6)]),(4,[(2,34,6)]),(8,[(2,34,6)]),(9,[(3,2,5)]),(5,[(3,2,5)]),(5,[(3,0,5)]),(3,[(2,17,6)]),(5,[(0,5,6)]),(1,[(0,5,6)]),(7,[(0,5,6),(2,3,7)]),(8,[(0,5,6)]),(0,[(1,0,1),(2,76,2)]),(8,[(1,0,1)]),(9,[(2,76,2)]),(2,[(1,5,6)]),(3,[(1,5,6)]),(1,[(1,1,3)]),(6,[(1,5,6)]),(6,[(2,5,6)]),(3,[(3,57,5)]),(7,[(1,27,1)]),(0,[(1,1,5),(1,2,6)]),(4,[(1,1,5)]),(11,[(1,2,6)]),(0,[(1,2,6)]),(7,[(3,4,6)]),(9,[(1,138,0)]),(0,[(1,2,6),(1,2,5)]),(0,[(1,1,5)]),(0,[(1,1,5),(3,2,5)]),(3,[(3,2,5)]),(0,[(1,1,5),(3,2,17)]),(8,[(1,1,5)]),(9,[(3,2,17)]),(1,[(1,0,5)]),(9,[(1,138,5)]),(7,[(1,25,5)]),(4,[(1,25,5)]),(8,[(1,25,5)]),(3,[(3,2,17)]),(7,[(3,2,5)]),(8,[(1,103,0)]),(0,[(1,2,6),(1,6,5)]),(0,[(3,2,5),(1,103,1)]),(8,[(1,103,1)]),(6,[(3,2,5),(1,103,1)]),(4,[(0,35,5)]),(5,[(1,2,6),(0,35,5)]),(8,[(0,63,5)]),(4,[(3,35,5)]),(8,[(3,35,5)]),(8,[(2,48,6)]),(7,[(3,2,6)]),(8,[(1,86,0)]),(4,[(1,86,5)]),(8,[(1,86,5)]),(3,[(2,71,6)]),(4,[(0,86,5)]),(8,[(1,5,6)]),(3,[(1,2,5)]),(0,[(1,0,1),(1,2,5)]),(2,[(3,1,5)]),(9,[(2,50,6)]),(4,[(1,1,6)]),(0,[(1,1,6)]),(2,[(1,1,5)]),(3,[(0,117,5)]),(3,[(1,3,4)]),(4,[(1,3,4)]),(1,[(1,3,4)]),(2,[(1,3,4)]),(5,[(2,5,6)]),(18,[]),(7,[(1,6,5)]),(9,[(3,0,50)]),(0,[(0,5,6),(1,0,7)]),(4,[(0,5,6),(1,0,7)]),(8,[(0,5,6),(1,0,7)]),(3,[(1,4,5)]),(4,[(1,4,5)]),(1,[(1,4,5)]),(5,[(1,4,5)]),(2,[(0,5,6)]),(1,[(3,6,5)]),(3,[(0,6,5),(1,2,7)]),(7,[(0,6,5),(1,2,7)]),(0,[(0,6,5),(1,2,7)]),(3,[(0,76,6)]),(0,[(1,0,1),(0,76,6)]),(4,[(1,103,1)]),(0,[(0,5,6),(2,1,7)]),(9,[]),(7,[(1,22,6)]),(7,[(0,6,5),(1,4,7)]),(19,[]),(16,[]),(0,[(2,5,6)]),(9,[(2,5,6)]),(0,[(0,5,6)]),(4,[(0,5,6)]),(0,[(1,0,1)]),(5,[(1,0,1)]),(4,[(1,0,1)]),(5,[(3,4,6)]),(3,[(1,0,3)]),(4,[(1,1,3)]),(0,[(1,0,5)]),(9,[(1,0,5)]),(0,[(3,0,5)]),(9,[(3,0,5)]),(0,[(1,5,6)]),(9,[(1,5,6)]),(3,[(1,3,5)]),(4,[(1,3,5)]),(6,[(1,3,5)]),(5,[(1,1,5)]),(0,[(3,2,5)]),(6,[(3,2,5)]),(0,[(3,2,6)]),(6,[(1,2,5)]),(0,[(1,2,5)])] : List PoolSpec)).map some)
def B_44_5 : BT (List (List Nat)) := BT.empty
lemma B_44_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 5 xs.toFinset) B_44_5 := .empty
def P_44_6 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]
def N_44_6 : List NodeSpec := [([9,0,1,2,3,11,4],[],[]),([14,1,2,3,4,5,6],[],[]),([9,0,1,2,3,15,4],[0,1,2,3,4],[]),([16,0,1,2,3,4,8],[2],[]),([18,12,1,2,3,4,5],[],[]),([20,1,2,3,4,5,6],[],[]),([9,0,1,2,3,4,13],[1,2,3,4],[]),([21,24,1,3,4,5,6],[],[]),([9,12,1,2,3,4],[1,2],[]),([9,0,1,2,3,4],[2],[]),([26,27,1,3,4,28,5],[5],[]),([31,9,1,2,3,4],[1],[]),([9,0,1,2,3,32],[2],[]),([1,2,3,4,33,30,8],[6],[]),([1,3,4,30,36,8],[2],[]),([1,2,3,4,38,8],[2,4,7,8],[]),([9,0,1,2,3,4,33],[0],[]),([21,12,1,3,4,5,6],[],[]),([0,41,1,2,3,4],[2,9],[]),([42,9,1,2,3,4],[1,2],[]),([44,24,1,2,3,5,6],[],[]),([45,1,2,4,30,8],[2],[]),([1,2,3,4,22,47],[2,4,10,11,12],[]),([49,24,1,3,4,5,6],[],[]),([1,2,3,4,30,8],[2,13],[]),([9,24,1,2,3,4],[2],[]),([9,1,2,3,4,30],[1,2],[]),([0,1,2,3,4,17,47],[2,14],[]),([1,2,3,4,30,50,8],[],[]),([1,2,3,4,30,8,13],[2,4,10,15],[]),([45,9,0,1,2,4],[2],[]),([0,1,2,3,4,51,8],[2,16],[]),([9,0,1,2,3,4,50],[],[]),([52,2,3,4,30,8],[2],[]),([0,1,2,53,32,8],[2],[]),([1,2,3,4,54,8],[2],[]),([52,9,0,2,3,4],[2],[]),([31,1,2,3,4,8],[2],[]),([1,2,3,30,32,8],[2],[]),([56,24,1,3,4,5,6],[],[]),([59,2,3,43,4,5,6],[17],[]),([0,1,4,36,53,8],[2],[]),([60,9,1,2,3,4],[1,2],[]),([9,0,1,3,4,36],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_6 : checkNodesBT W_44 g_44 F_44 P_44_6 A_44 B_44_5 6 N_44_6 = true := by decide +kernel
def B_44_6 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_6
set_option maxRecDepth 500000 in
lemma B_44_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 6 xs.toFinset) B_44_6 :=
  buildBucketsBT_sound (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_5_ok C_44_6
def P_44_7 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 [1,2,3,4,5,10,15,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98]
def N_44_7 : List NodeSpec := [([24,1,2,3,4,5,6,13],[18,19],[0]),([24,1,2,3,55,4,5,6],[19,20],[0]),([24,1,61,2,3,4,5,6],[21],[]),([12,1,2,3,4,5,6,19],[],[0]),([9,0,1,2,3,4,5],[2,22,23,24,25],[0]),([9,0,1,2,3,4,7],[2,24,25,26],[0,1]),([62,10,0,1,2,3,11,4],[27],[0]),([0,1,2,3,4,7,8,13],[2,4,28,29],[0]),([0,1,2,3,4,7,8],[2],[0]),([0,1,3,4,7,36,8],[2,25,30],[0]),([45,0,1,4,5,36,6],[2],[]),([52,0,3,4,5,36,6],[2],[]),([60,1,2,3,4,7,8],[2,28],[0]),([60,1,2,3,5,32,6],[],[]),([60,1,3,4,5,36,6],[2],[]),([1,2,3,4,7,30,8],[2,24,25,26,31],[0,1]),([1,2,3,5,30,32,6],[2],[0]),([52,2,3,4,5,30,6],[2],[0]),([1,2,3,4,5,30,8],[2,15,22,24,25,31],[0]),([1,2,3,4,30,8],[2,4,10,15,22,31,32,33],[0,1]),([62,64,0,1,2,3,4,6],[34],[]),([62,10,0,1,2,3,4,50],[],[0]),([65,0,1,2,3,4,5,8],[2],[]),([0,1,3,4,5,36,8],[2,22,25],[]),([24,1,2,3,4,5,50,6],[35],[]),([60,52,2,3,4,5,6],[],[]),([0,1,3,4,5,67,6],[2,36,37],[]),([0,1,2,3,4,7,50,8],[],[0]),([0,1,3,4,5,36,50,6],[38],[]),([24,1,2,3,4,5,48,6],[19,20],[0]),([62,69,0,2,3,4,5,6],[26],[]),([24,1,2,3,4,33,5,6],[20],[]),([62,0,2,3,4,70,6],[2],[]),([0,1,2,3,4,33,7,8],[39],[0]),([0,1,3,4,33,5,36,6],[40],[]),([1,2,3,4,33,5,30,6],[41],[0]),([21,0,1,3,4,5,6,8],[4],[0]),([24,1,2,3,4,5,6,19],[42],[]),([0,1,2,5,53,32,6],[2],[0]),([59,1,2,3,4,5,6],[2,17,43],[0]),([0,1,73,3,4,5,6],[],[]),([45,0,2,4,5,70,6],[2],[]),([0,1,3,4,5,75,6],[2,25,44],[]),([39,76,2,3,43,4,5,6],[45,46,47],[1]),([0,1,3,4,5,78,6],[2],[]),([45,0,1,2,4,7,8],[2,39,48],[0]),([24,1,2,3,4,5,6],[],[]),([0,1,2,3,4,22,35,8],[2,10],[]),([52,0,2,3,4,7,8],[2,49],[0]),([1,2,3,4,5,30,6],[2],[0]),([62,10,0,1,2,3,4],[2],[0]),([1,2,3,4,74,22,6],[2,50],[]),([44,0,1,2,3,5,6,29],[51],[]),([1,79,2,25,3,4,5,6],[],[]),([0,1,80,3,4,5,35],[2,4],[]),([0,1,2,3,4,37,8],[2,4,52,53],[0]),([0,1,3,4,5,36,6,63],[54],[]),([0,1,3,4,83,5,6],[36,55],[]),([40,0,1,2,3,4,8],[2],[0]),([44,39,0,1,2,3,5,6],[51],[]),([0,1,2,3,7,32,8],[2,25,26],[0,1]),([0,1,2,3,4,74,8],[2,56],[0]),([1,84,2,3,4,5,29],[2,10,22,57,58],[1]),([1,2,3,4,5,30,50,6],[59],[0]),([49,0,1,3,4,5,22,6],[60],[]),([39,1,79,2,3,4,5,6],[],[]),([85,0,1,2,3,4,5],[],[]),([88,1,2,3,4,5,6],[2],[]),([12,1,2,3,4,7,8],[2,28],[0]),([26,0,1,3,4,28,5,6],[61,62,63],[0]),([60,45,1,2,4,5,6],[],[]),([24,1,2,3,4,5,34,6],[19],[]),([62,0,89,1,2,3,4],[2],[0]),([62,9,0,1,2,3,4],[2,22,24,25,64,65,66],[1]),([49,0,1,3,4,5,6,8],[25,60],[0]),([0,1,3,4,5,36,6],[2],[]),([9,0,1,2,3,4,8],[2,3,4,22,23],[0,1]),([91,0,1,2,3,4,5],[],[]),([92,0,1,2,3,4,5,68],[62,67],[]),([62,44,0,1,2,3,5,6],[22],[]),([0,1,2,3,4,94,6],[2,4,68,69,70,71],[]),([44,0,1,2,3,5,22,6],[51],[]),([95,0,1,2,3,4,5,6],[],[]),([96,0,1,2,3,4,5,35],[61],[]),([62,1,2,3,4,30,6],[2],[0]),([0,1,97,3,4,5,6],[22,72],[]),([0,1,84,2,3,4,5,35],[2,61,73,74],[1]),([12,1,2,3,4,5,6,13],[75],[0]),([1,2,3,4,5,38,6],[2,4,76,77,78],[0]),([0,1,98,3,4,5,6],[2],[]),([0,1,3,5,36,32,6],[2],[]),([62,0,1,99,2,3,4],[2],[]),([49,0,1,3,4,5,6,29],[60],[]),([39,1,2,3,4,100,6],[2],[]),([0,1,2,3,4,5,51,6],[2,50,79],[0]),([101,0,1,2,3,4,5,6],[80],[]),([102,0,2,3,43,4,5,6],[81],[]),([0,104,1,3,4,28,5,6],[82],[]),([44,0,1,2,3,5,6,8],[22,51],[0]),([0,1,3,4,37,34,6],[2,24],[]),([49,27,0,1,3,4,5,6],[60],[]),([0,1,3,4,28,5,6,105],[62,83],[1]),([1,2,3,4,22,29,8],[2,10,22,50],[0]),([0,1,3,4,5,107,6],[2,22,84],[]),([24,1,2,3,43,4,5,6],[21,85],[0]),([1,3,4,5,30,36,6],[2],[0]),([0,1,3,4,5,108,35],[2,4],[]),([24,1,2,3,4,7,8],[2],[0]),([0,1,2,3,4,5,110,6],[2,50],[]),([45,1,2,4,5,30,6],[2],[0]),([0,1,2,3,4,5,47],[2,4,86,87,88,89],[0]),([26,27,1,2,3,4,5],[2,5,90],[0]),([24,1,2,3,4,5,17,6],[21],[]),([12,1,2,3,4,5,35,8],[2,91],[]),([9,0,1,2,3,4],[1,2,3,4,22,23],[0,1]),([0,1,4,5,36,53,6],[2],[0]),([0,1,2,3,4,17,35,8],[92],[0]),([24,1,2,3,4,5,35,8],[2,93],[]),([62,0,1,2,3,4,17,8],[26],[]),([18,0,1,2,3,4,5,8],[2,94],[]),([0,1,2,3,4,30,8],[2,28,31],[]),([62,10,0,1,2,3,4,33],[95],[0]),([39,27,1,2,3,4,8],[2],[]),([0,1,46,3,4,34,6],[2,24,96,97,98],[]),([111,1,2,3,4,5,6],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_7 : checkNodesBT W_44 g_44 F_44 P_44_7 A_44 B_44_6 7 N_44_7 = true := by decide +kernel
def B_44_7 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_7
set_option maxRecDepth 500000 in
lemma B_44_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 7 xs.toFinset) B_44_7 :=
  buildBucketsBT_sound (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_6_ok C_44_7
def P_44_8 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 [2,4,10,19,20,21,22,24,25,26,28,29,35,36,40,42,45,46,47,49,50,51,57,60,61,62,67,75,85,94,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316]
def N_44_8 : List NodeSpec := [([62,10,0,1,2,3,4,5],[2,22,24,25,99],[0]),([0,1,2,3,4,7,5,6],[2,24,26,45,50,61,62,100,101,102],[0,1]),([62,0,1,2,3,4,112,5,6],[62,103],[1]),([0,1,113,2,3,4,5,6],[2,22,26,50,104,105],[]),([62,0,1,114,2,3,4,5,6],[2,22,106],[]),([0,1,114,2,3,4,5,6],[2,4,22,50,106,107,108],[]),([0,115,1,2,3,4,5,6],[2,10,22,45,61,109],[]),([0,1,2,3,4,5,6,8,13],[2,25,110,111],[0,1]),([116,0,1,2,3,4,5,6],[2,4,22,36,50,105,112,113],[]),([0,1,2,3,4,5,6,8,19],[2,22,26,110],[0]),([24,1,2,3,4,5,6,8],[2,19,21,35,50,114],[0,1]),([24,0,1,2,3,4,5,6],[2,4,21,22,36,45,61,108,110],[]),([24,1,2,3,4,5,6],[2,19,20,21,85,115,116,117],[0,1]),([12,1,2,3,4,5,6,8],[2,75,110,118,119,120],[0,1]),([0,1,2,3,4,7,5,8],[2,22,24,25,49],[0]),([0,1,2,3,4,7,8],[2,4,22,28,29,49,121,122],[0,1]),([62,0,1,2,3,4,5,6],[2,22,24,45,50,100,102,108],[0]),([0,1,3,4,28,5,6,35],[4,36,123,124,125],[1]),([0,1,2,3,43,4,5,6,29],[22,46,126,127],[0]),([62,0,1,2,3,4,5,50,6],[26,103],[0]),([0,1,2,3,4,5,22,17,6],[2,22,45,128],[]),([39,0,1,2,3,4,5,6,117],[2,22,26,45,129],[]),([103,0,1,3,4,5,34,6],[2,36,61,130,131],[]),([118,0,1,2,3,4,5,6],[2,22,24,45,50,61,101,102,108,132],[1]),([0,1,2,3,4,5,22,6,68],[26,36,133,134,135,136],[0,1]),([62,0,1,2,3,4,7,6],[2,26,105,137],[0]),([92,0,1,2,3,4,5,6],[2,10,22,45,50,61,67,138],[0]),([120,0,1,2,3,4,5,6],[2,36,45,50,61,62,139,140,141],[]),([0,1,2,3,4,5,48,6,8],[25,108,111,142,143],[0]),([0,1,2,3,4,74,5,6],[2,22,24,25,45,61,101,102,108,144],[0,1]),([102,0,1,2,3,4,5,6],[2,4,61,108,145,146],[0]),([0,1,99,2,3,4,5,6],[2,4,50,61,100,147,148],[0]),([39,0,1,2,3,4,5,17,6],[2,42,45,128],[]),([121,0,1,2,3,4,5,6],[2,45,50,61,108,140,149],[]),([62,0,1,2,3,4,22,6],[2,22,50,109],[]),([122,0,1,2,3,4,5,6],[2,22,36,45,150,151,152],[]),([0,1,2,3,4,5,90,6],[2,4,22,108,153,154,155],[0,1]),([0,1,25,3,4,28,5,6],[4,36,61,123,131,156,157,158],[0,1]),([0,1,123,2,3,4,5,6],[2,22,26,50,101,159,160,161],[]),([39,0,1,2,3,4,5,50,6],[162,163,164],[]),([0,1,2,3,4,33,5,22,6],[36,165,166,167],[]),([0,1,2,3,4,5,22,48,6],[2,101,108,142,168],[0]),([0,1,124,2,3,4,5,6],[2,4,22,108,169,170,171],[]),([0,1,25,3,4,5,34,6],[2,36,61,130,131,152,172],[0]),([26,0,1,2,3,4,5,6],[2,22,36,45,100,173,174,175],[0]),([1,76,2,3,4,5,6,29],[2,22,50,126,176],[0]),([39,1,76,2,3,4,5,6],[2,45,47,170,177],[0,1]),([0,1,2,3,125,4,5,6],[2,45,50,62,102,140,178,179,180],[1]),([0,1,2,3,4,5,22,6,35],[2,10,181],[0]),([126,0,1,2,3,4,5,6],[2,4,22,102,105,182,183,184],[]),([0,1,25,3,4,5,6,35],[2,22,36,61,131,181,185],[0]),([0,1,2,3,4,5,34,6,8],[2,4,24,111,152],[0]),([127,0,1,2,3,4,5,6],[2,26,100,101,186],[]),([96,0,1,2,3,4,5,6],[2,4,50,61,108,187,188],[0]),([0,1,2,3,4,5,58,6],[2,4,50,61,108,189,190,191],[0,1]),([0,1,128,2,3,4,5,6],[2,24,50,101,102,108,192,193],[1]),([129,0,1,2,3,4,5,6],[2,10,22,36,61,101,105,176,194,195,196],[]),([62,0,1,2,3,4,5,6,68],[26,62,135,197,198],[0]),([62,10,0,1,2,3,4],[2,4,22,24,25,99],[0,1]),([0,1,76,2,3,4,5,6,35],[2,50,176,199,200],[0]),([0,1,2,3,4,5,30,6],[2,10,22,61,201,202],[0]),([44,0,1,2,3,5,6],[22,36,51,203,204],[0]),([130,0,1,2,3,4,5,6],[2,36,45,50,61,100,108,205,206],[]),([131,0,1,2,3,4,5,6],[2,4,50,62,101,105,207,208,209],[]),([0,1,2,3,4,5,100,6],[2,4,22,36,45,61,108,210],[0]),([0,1,2,3,4,5,70,6],[2,22,26,211,212,213],[]),([39,1,2,3,4,5,22,6],[2,50,214,215],[]),([0,1,2,3,4,5,22,50,6],[2,36,102,164],[]),([39,0,1,2,3,43,4,5,6],[22,45,46,101,108,170,216,217],[0]),([0,1,2,3,4,5,22,6,117],[2,22,26,129],[]),([39,0,1,2,3,4,132,5,6],[62,162,218],[]),([0,1,2,3,43,4,5,22,6],[22,46,134,136,216],[0]),([133,0,1,2,3,4,5,6],[2,22,24,45,100,102,108],[]),([134,0,1,2,3,4,5,6],[2,4,10,22,36,61,101,105,168,219,220],[]),([39,0,1,2,3,4,5,6,63],[2,101,108,221],[1]),([39,0,1,2,3,4,6,8],[2,4,22,110],[0]),([39,0,1,124,2,3,4,5,6],[2,169,170],[]),([135,0,1,2,3,4,5,6],[2,4,22,24,36,45,50,61,100,222,223],[]),([103,0,1,3,4,28,5,6],[4,36,123,224,225],[0]),([40,0,1,2,3,4,5,6],[2,24,26,45,61,62,100,101,102],[0,1]),([39,0,1,2,3,4,33,5,6],[36,165,167,226],[]),([18,0,1,2,3,4,5,6],[2,4,22,45,50,61,94,108,227],[0]),([45,0,1,2,4,7,5,6],[2,26,46,100,167,228,229,230,231],[0]),([1,2,3,4,5,22,6,29],[2,10,22],[0,1]),([136,0,1,2,3,4,5,6],[2,4,61,62,101,176,232,233,234],[]),([0,1,2,3,4,5,50,6,8],[2,36,164,235],[0]),([0,1,2,3,43,4,5,6,8],[22,46,108,216,236,237,238],[0]),([62,0,1,2,3,43,4,5,6],[22,45,46,106,108,237,239],[0]),([0,137,1,2,3,4,5,6],[2,24,50,101,102,108,240],[]),([0,1,79,2,3,4,5,6],[22,26,241],[0]),([0,1,2,3,4,33,5,6,8],[36,143,165,167],[0]),([102,0,1,2,3,4,5,17,6],[2,45,50,128],[]),([0,1,2,3,4,5,17,6,35],[4,22,199,242,243],[0]),([86,0,1,3,4,5,6,35],[2,36,125,131,244,245],[]),([62,0,1,2,3,4,5,17,6],[2,22,26,45],[0]),([0,139,1,2,3,4,5,6],[2,36,101,108,246,247],[]),([0,1,3,4,5,34,6,35],[2,4,22,36,131,248],[0]),([103,0,1,2,3,4,5,17,6],[243,249,250,251],[]),([140,0,1,2,3,4,5,6],[2,4,50,62,101,105,252,253,254],[1]),([0,1,2,3,4,5,22,6,63],[2,10,101,108,221,255],[]),([0,1,2,3,4,5,141,6],[2,36,101,108,256],[]),([0,1,2,3,4,5,142,6],[2,22,36,101,105,257,258,259],[]),([140,0,1,2,3,4,5,17,6],[249,252,260],[]),([0,104,1,2,3,4,5,6],[2,22,36,45,101,261,262],[0]),([0,1,2,3,4,5,35,8],[2,4,112,263],[0,1]),([0,1,2,3,4,5,17,6,8],[2,22,128,236],[0]),([0,1,143,2,3,4,5,6],[2,22,50,251,264,265,266],[]),([0,1,2,3,4,37,5,6],[2,4,22,45,50,101,102,108,267,268],[0,1]),([0,1,2,3,4,144,5,6],[2,50,62,102,140,269],[1]),([0,1,2,3,4,5,6,19],[2,4,22,26,50,105,108],[0]),([145,0,1,2,3,4,5,6],[2,4,22,50,102,105,270,271],[]),([146,0,1,2,3,4,5,6],[2,25,36,45,50,61,62,140,272],[]),([0,147,1,2,3,4,5,6],[2,22,36,45,101,273,274],[]),([0,1,2,3,4,5,148,6],[2,22,36,45,275,276],[]),([149,0,1,2,3,4,5,6],[2,24,50,100,102,108,277],[]),([87,0,1,2,3,4,5,6],[2,26,50,62,100,101,102,105,278],[0,1]),([86,0,1,2,3,4,5,8],[2,22,111,279],[]),([0,1,76,2,3,4,5,34,6],[2,4,24,50,280,281],[]),([62,71,0,1,2,3,4,6],[2,45,197,282],[0]),([65,0,1,2,3,4,5,6],[2,36,45,50,61,100,108,283],[0,1]),([0,1,2,3,4,5,34,6,117],[22,26,280,284],[]),([103,0,1,2,3,4,5,6,117],[2,22,26,284,285],[]),([62,0,1,2,3,4,17,6],[2,22,26,45,106,286],[0]),([62,0,1,2,3,4,5,6,117],[2,22,26,45,197],[]),([1,2,3,4,7,5,30,6],[24,25,26,50,201],[0,1]),([0,1,2,3,4,150,5,6],[2,24,50,101,102,108,287],[1]),([0,1,2,3,4,33,7,5,6],[62,165,167,228,288,289,290,291],[0,1]),([62,0,1,2,3,4,33,5,6],[36,167,292],[0]),([49,0,1,3,4,5,6],[25,60,108,140,293],[0,1]),([62,0,1,2,3,4,5,8],[2,24,105],[0]),([0,1,2,3,4,5,29,8],[2,10,294],[0,1]),([151,0,1,2,3,4,5,6],[2,36,45,50,101,108,295],[]),([1,2,3,4,5,30,6],[2,4,10,22,201,296,297,298],[0,1]),([0,1,2,3,4,7,5,50,6],[62,102,164,299,300,301,302,303],[0,1]),([62,39,0,1,2,3,4,6],[2,22,50,109],[0]),([62,0,1,2,3,4,5,6,63],[2,100,108,304],[0,1]),([60,1,2,3,4,7,5,6],[2,24,25,26,202],[0,1]),([39,27,1,2,3,4,5,6],[2],[0,1]),([0,1,3,4,5,36,6],[2,4,22,25,40,305,306],[0,1]),([39,0,1,2,3,4,5,6,68],[2,26,62,133,135,170],[1]),([0,1,3,4,7,5,36,6],[2,25,26,61,305,306,307],[0,1]),([0,1,2,3,4,5,6,8],[2,4,22,36,45,50,61,108],[0]),([0,1,84,2,3,4,5,6],[2,4,22,36,50,57,61,62,100,101,308,309],[0,1]),([103,0,1,143,2,3,4,5,6],[264,310],[]),([52,0,2,3,4,7,5,6],[2,24,46,140,211,311,312],[0,1]),([0,1,2,3,4,5,6,23],[2,10,22,45,61,313],[0]),([0,1,2,3,7,5,32,6],[2,24,25,26,36,62,314,315,316],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_8 : checkNodesBT W_44 g_44 F_44 P_44_8 A_44 B_44_7 8 N_44_8 = true := by decide +kernel
def B_44_8 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_8
set_option maxRecDepth 500000 in
lemma B_44_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 8 xs.toFinset) B_44_8 :=
  buildBucketsBT_sound (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_7_ok C_44_8
def P_44_9 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 [2,4,10,22,24,25,26,36,45,46,50,61,62,100,101,102,105,106,108,109,110,128,131,134,140,142,143,152,164,165,166,167,170,176,202,211,216,217,220,231,236,239,243,246,249,251,261,273,279,280,288,289,299,300,302,312,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341]
def N_44_9 : List NodeSpec := [([62,0,1,2,3,4,5,6],[2,4,24,25,45,50,61,100,102,106,108,109,239,317,318],[0,1]),([0,1,2,3,4,7,5,6],[2,4,22,45,50,61,62,100,101,102,202,211,231,319,320],[0,1]),([0,1,76,2,3,4,5,6],[2,45,50,101,108,140,176,312,321,322,323],[0,1]),([138,0,1,2,3,4,5,6],[2,36,50,100,101,102,108,246,312,324],[0]),([0,1,2,3,119,4,5,6],[2,50,100,108,131,140,325],[0,1]),([0,1,2,3,43,4,5,6],[22,45,46,50,62,108,131,216,326],[0,1]),([0,1,2,3,4,5,50,6],[36,108,164,299,300,302,312],[0,1]),([0,1,2,3,4,5,22,6],[2,10,24,36,50,108,134,166,220,327,328],[0,1]),([39,0,1,2,3,4,5,6],[2,4,24,25,45,50,61,101,102,108,170,217,329,330],[0,1]),([0,1,2,3,4,5,6,8],[2,36,50,108,110,143,236,279,331,332],[0,1]),([0,1,2,3,4,33,5,6],[36,50,131,165,167,288,289,312],[0,1]),([0,1,2,3,4,5,48,6],[25,100,108,131,140,142,333,334,335],[0,1]),([0,1,2,3,4,5,17,6],[22,45,128,140,243,249,312,336],[0,1]),([103,0,1,2,3,4,5,6],[2,36,50,61,62,101,102,105,131,251,261,337,338],[0,1]),([86,0,1,2,3,4,5,6],[2,22,26,36,50,61,62,100,101,105,131,273,339],[0,1]),([0,1,2,3,4,5,34,6],[4,24,36,61,131,152,280,340,341],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_9 : checkNodesBT W_44 g_44 F_44 P_44_9 A_44 B_44_8 9 N_44_9 = true := by decide +kernel
def B_44_9 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_9
set_option maxRecDepth 500000 in
lemma B_44_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 9 xs.toFinset) B_44_9 :=
  buildBucketsBT_sound (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_8_ok C_44_9
def P_44_10 : BT (Option BoundPool) := buildPoolsSubBT 9 W_44 r_44 S_44 ps_44 [45,50,61,62,100,101,102,105,131,312]
def N_44_10 : List NodeSpec := [([0,1,2,3,4,5,6],[45,50,61,62,100,101,102,105,131,312],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_44_10 : checkNodesBT W_44 g_44 F_44 P_44_10 A_44 B_44_9 10 N_44_10 = true := by decide +kernel
def B_44_10 : BT (List (List Nat)) := buildBucketsBT W_44 N_44_10
set_option maxRecDepth 500000 in
lemma B_44_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_44 10 xs.toFinset) B_44_10 :=
  buildBucketsBT_sound (by decide) gp_44 W_44_ok (buildPoolsSubBT_sound S_44_ok) A_44_ok B_44_9_ok C_44_10
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_44_ok : forestRootCheck r_44 g_44 [(VAR 0,32,33),(VAR 1,16,18),(VAR 2,8,12),(VAR 3,4,12),(VAR 4,2,18),(VAR 5,1,33),(VAR 6,1,65)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_44_in : bucketContainsBT B_44_10 r_44 = true := by decide +kernel
lemma low_44 : Lower r_44 g_44 11 := lower_of_forestBT root_44_ok B_44_10_ok root_44_in
def g_45 := 0xfffefee0fffefee0fffefee0fffefee0fffefee0fffefee0fffefee0fffefee0
def r_45 : List Nat := varsOf 31
set_option maxHeartbeats 0 in
lemma low_45 : Lower r_45 g_45 8 := by
  have hc : Lower (varsOf 30) 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0fffcfcc0 7 := carry_of (swaps := [(0,4),(1,4),(2,4),(3,4)]) (by decide +kernel) low_3
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,4,5)]) (by decide +kernel) hc
def g_46 := 0xfffffffafffceac0fffffffafffceac0fffffffafffceac0fffffffafffceac0
def r_46 : List Nat := varsOf 63
def p_46 : List Nat := [6,6,7,7,9,9,11,11,13,13,14,14,18,18,19,19,20,20,21,21,24,24,25,26,28,33,33,35,35,36,36,37,38,40,40,42,42,44,48,48,49,50]
def q_46 : List Nat := [4,2,5,3,8,1,10,3,12,5,12,10,16,2,17,3,16,4,17,5,16,8,17,10,12,32,1,34,3,32,4,5,34,32,8,34,10,12,32,16,17,34]
def F_46 : Nat := fullMask 42
set_option maxHeartbeats 0 in
lemma gp_46 : goodPairs g_46 p_46 q_46 := goodPairs_of (by decide +kernel)
def W_46 : BT Decor := buildWiresBT 6 (mkBase p_46 q_46 r_46) [(1,2,3),(1,3,4),(1,2,5),(0,7,8),(1,4,5),(0,6,10),(1,2,4),(1,3,5),(3,3,8),(1,1,5),(3,3,10),(3,1,12),(3,0,13),(1,6,4),(2,6,5),(1,3,8),(2,7,5),(1,22,2),(1,16,2),(3,2,7),(2,25,5),(1,12,5),(3,3,27),(1,17,5),(3,6,10),(2,20,4),(1,3,10),(1,14,4),(1,19,5),(1,0,5),(1,0,4),(1,20,4),(1,0,3),(2,19,5),(2,1,5),(2,0,4),(3,3,15),(1,1,4),(1,1,2),(1,0,2),(1,0,1)]
lemma W_46_ok : btAll (fun x => faithful p_46 q_46 x ∧ x.1 < 2^256) W_46 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_46 : List (List (Nat × Nat)) := [[],[(0,1),(2,3),(4,5)]]
def A_46 : BT (List (Nat × Nat)) := btOfList 1 al_46
set_option maxHeartbeats 0 in
lemma A_46_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_46 = g_46) A_46 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_46_0 : Slice r_46 g_46 (identDom 0 1) 8 := by
  have hc : Lower (varsOf 61) 0xfffffffafffaaaa0fffffffafffaaaa0fffffffafffaaaa0fffffffafffaaaa0 8 := carry_of (swaps := [(0,2),(1,5),(3,5),(4,5)]) (by decide +kernel) low_45
  exact slice_ident (u := 0) (v := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_1 : Slice r_46 g_46 (identDom 0 2) 8 := by
  have hc : Lower (varsOf 59) 0xffffffaaffeeaa88ffffffaaffeeaa88ffffffaaffeeaa88ffffffaaffeeaa88 8 := carry_of (swaps := [(0,3),(1,3),(2,5)]) (by decide +kernel) low_4
  exact slice_ident (u := 0) (v := 2) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_2 : Slice r_46 g_46 (identDom 1 3) 8 := by
  have hc : Lower (varsOf 55) 0xfffffefefcfcc8c8fffffefefcfcc8c8fffffefefcfcc8c8fffffefefcfcc8c8 8 := carry_of (swaps := [(1,3),(2,3),(3,5),(4,5)]) (by decide +kernel) low_4
  exact slice_ident (u := 1) (v := 3) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_3 : Slice r_46 g_46 (subcubeFast 1 0) 7 := by
  have hc : Lower (varsOf 62) 0xfffffff0fffcc0c0fffffff0fffcc0c0fffffff0fffcc0c0fffffff0fffcc0c0 7 := carry_of (swaps := [(0,5),(1,5),(2,3),(3,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_4 : Slice r_46 g_46 (subcubeFast 2 0) 7 := by
  have hc : Lower (varsOf 61) 0xfffffffafff0aa00fffffffafff0aa00fffffffafff0aa00fffffffafff0aa00 7 := carry_of (swaps := [(1,5),(2,5),(4,5)]) (by decide +kernel) low_19
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_5 : Slice r_46 g_46 (subcubeFast 4 0) 7 := by
  have hc : Lower (varsOf 59) 0xffffffaaffccaa00ffffffaaffccaa00ffffffaaffccaa00ffffffaaffccaa00 7 := carry_of (swaps := [(0,1),(2,5),(3,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_6 : Slice r_46 g_46 (subcubeFast 8 0) 7 := by
  have hc : Lower (varsOf 55) 0xfffffafafcfcc0c0fffffafafcfcc0c0fffffafafcfcc0c0fffffafafcfcc0c0 7 := carry_of (swaps := [(3,5),(4,5)]) (by decide +kernel) low_8
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_7 : Slice r_46 g_46 (subcubeFast 16 0) 7 := by
  have hc : Lower (varsOf 47) 0xfffafffaeac0eac0fffafffaeac0eac0fffafffaeac0eac0fffafffaeac0eac0 7 := carry_of (swaps := [(0,1),(2,3),(4,5)]) (by decide +kernel) low_9
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_8 : Slice r_46 g_46 (subcubeFast 32 0) 7 := by
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) low_9
set_option maxHeartbeats 0 in
lemma sl_46_9 : Slice r_46 g_46 (subcubeFast 7 0) 4 := by
  have hc : Lower (varsOf 56) 0xffffff00ff000000ffffff00ff000000ffffff00ff000000ffffff00ff000000 4 := carry_of (swaps := [(0,3),(1,4),(2,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 7) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_10 : Slice r_46 g_46 (subcubeFast 11 0) 4 := by
  have hc : Lower (varsOf 52) 0xfffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000fffff0f0f0f00000 4 := carry_of (swaps := [(0,3),(1,4),(2,3),(3,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 11) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_11 : Slice r_46 g_46 (subcubeFast 41 0) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 41) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_12 : Slice r_46 g_46 (subcubeFast 40 1) 4 := by
  have hc : Lower (varsOf 22) 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0 4 := carry_of (swaps := [(0,3),(1,3),(2,3),(3,4)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 40) (o := 1) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_13 : Slice r_46 g_46 (subcubeFast 22 0) 4 := by
  have hc : Lower (varsOf 41) 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00 4 := carry_of (swaps := [(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 22) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_46_14 : Slice r_46 g_46 (subcubeFast 20 2) 4 := by
  have hc : Lower (varsOf 41) 0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00 4 := carry_of (swaps := [(1,3),(2,4),(4,5)]) (by decide +kernel) low_0
  exact slice_fast_direct_f (z := 20) (o := 2) (by decide +kernel) hc
def S_46 : BT (Option (Nat × Nat)) := btOfList 4 [some (identDom 0 1,8),some (identDom 0 2,8),some (identDom 1 3,8),some (subcubeFast 1 0,7),some (subcubeFast 2 0,7),some (subcubeFast 4 0,7),some (subcubeFast 8 0,7),some (subcubeFast 16 0,7),some (subcubeFast 32 0,7),some (subcubeFast 7 0,4),some (subcubeFast 11 0,4),some (subcubeFast 41 0,4),some (subcubeFast 40 1,4),some (subcubeFast 22 0,4),some (subcubeFast 20 2,4)]
lemma S_46_ok : btAll (fun o => ∀ p, o = some p → Slice r_46 g_46 p.1 p.2) S_46 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_46_0) (forall_cons (fun _ h => by cases h; exact sl_46_1) (forall_cons (fun _ h => by cases h; exact sl_46_2) (forall_cons (fun _ h => by cases h; exact sl_46_3) (forall_cons (fun _ h => by cases h; exact sl_46_4) (forall_cons (fun _ h => by cases h; exact sl_46_5) (forall_cons (fun _ h => by cases h; exact sl_46_6) (forall_cons (fun _ h => by cases h; exact sl_46_7) (forall_cons (fun _ h => by cases h; exact sl_46_8) (forall_cons (fun _ h => by cases h; exact sl_46_9) (forall_cons (fun _ h => by cases h; exact sl_46_10) (forall_cons (fun _ h => by cases h; exact sl_46_11) (forall_cons (fun _ h => by cases h; exact sl_46_12) (forall_cons (fun _ h => by cases h; exact sl_46_13) (forall_cons (fun _ h => by cases h; exact sl_46_14) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))
def ps_46 : BT (Option PoolSpec) := btOfList 7 ((([(8,[]),(7,[]),(12,[]),(11,[]),(4,[]),(14,[]),(6,[]),(3,[(1,2,4),(3,1,12)]),(6,[(1,2,4),(3,1,12)]),(7,[(3,1,12),(1,17,5)]),(8,[(1,2,4),(3,1,12)]),(13,[]),(0,[]),(3,[(1,3,2),(1,2,4)]),(4,[(1,3,2),(1,3,5)]),(5,[]),(6,[(1,1,5),(1,4,5)]),(1,[]),(2,[]),(3,[(1,1,5),(1,4,5)]),(3,[(1,3,2)]),(3,[(1,1,5),(1,2,3),(1,2,5)]),(5,[(1,1,5)]),(1,[(1,1,5),(1,2,5)]),(6,[(1,1,5),(1,2,5)]),(5,[(1,1,5),(1,0,4),(1,4,5)]),(3,[]),(6,[(1,5,4)]),(7,[(3,3,10)]),(4,[(1,2,3)]),(8,[(1,2,3)]),(9,[]),(7,[(1,2,5)]),(0,[(1,2,4),(3,1,12)]),(3,[(2,1,5)]),(4,[(2,0,4)]),(8,[(2,0,4)]),(7,[(2,1,5)]),(5,[(2,1,5),(2,0,4)]),(3,[(1,1,5)]),(3,[(1,1,4)]),(4,[(1,0,5)]),(10,[]),(6,[(1,1,5)]),(8,[(3,3,15)]),(3,[(1,1,5),(1,2,5)]),(3,[(1,3,4)]),(5,[(1,1,5),(1,0,4)]),(7,[(1,1,5)]),(7,[(2,7,5)]),(4,[(1,3,4)]),(8,[(1,3,4)]),(4,[(1,0,4)]),(8,[(1,0,4)]),(5,[(1,0,4),(2,1,5)]),(3,[(1,1,2)]),(4,[(1,3,5)]),(6,[(1,1,2)]),(6,[(1,1,4)]),(5,[(1,3,5)]),(7,[(1,3,2)]),(4,[(1,3,2),(1,3,4)]),(2,[(1,2,3)]),(7,[(1,3,5)]),(7,[(1,2,3)]),(6,[(1,6,4)]),(5,[(2,6,5)]),(2,[(1,3,4)]),(4,[(1,4,5)]),(8,[(1,3,2)]),(3,[(1,2,4)]),(6,[(1,2,4)]),(7,[(1,12,5)]),(8,[(1,2,4)]),(5,[(3,3,8)]),(6,[(1,2,5)]),(3,[(1,4,5)]),(3,[(1,2,3)]),(8,[(1,1,2)]),(8,[(1,1,4)]),(6,[(1,0,2)])] : List PoolSpec)).map some)
def B_46_3 : BT (List (List Nat)) := BT.empty
lemma B_46_3_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 3 xs.toFinset) B_46_3 := .empty
def P_46_4 : BT (Option BoundPool) := buildPoolsSubBT 7 W_46 r_46 S_46 ps_46 []
def N_46_4 : List NodeSpec := [([0,1,6,9,10],[],[]),([0,1,11,7,8],[],[]),([0,1,11,12,13],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_4 : checkNodesBT W_46 g_46 F_46 P_46_4 A_46 B_46_3 4 N_46_4 = true := by decide +kernel
def B_46_4 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_4
set_option maxRecDepth 500000 in
lemma B_46_4_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 4 xs.toFinset) B_46_4 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_3_ok C_46_4
def P_46_5 : BT (Option BoundPool) := buildPoolsSubBT 7 W_46 r_46 S_46 ps_46 [0,1,2,3]
def N_46_5 : List NodeSpec := [([0,1,2,3,9,10],[0,1],[0]),([14,0,6,4,15,8],[],[]),([16,0,2,7,15,10],[],[]),([0,1,2,11,4,13],[2],[0]),([17,18,2,3,4,5],[],[]),([0,1,6,12,13,10],[3],[0]),([0,1,2,19,13,10],[0],[]),([20,14,0,1,2,4],[],[]),([0,1,6,7,8,10],[],[0]),([0,1,6,4,9,5],[],[0]),([0,1,2,7,21,10],[1],[]),([0,1,2,11,7,5],[1],[0]),([14,0,1,3,12,10],[],[]),([22,16,0,1,2,4],[2],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_5 : checkNodesBT W_46 g_46 F_46 P_46_5 A_46 B_46_4 5 N_46_5 = true := by decide +kernel
def B_46_5 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_5
set_option maxRecDepth 500000 in
lemma B_46_5_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 5 xs.toFinset) B_46_5 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_4_ok C_46_5
def P_46_6 : BT (Option BoundPool) := buildPoolsSubBT 7 W_46 r_46 S_46 ps_46 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26]
def N_46_6 : List NodeSpec := [([0,1,2,23,3,4,5],[4,5],[]),([16,0,1,2,4,7,5],[2,6],[0]),([0,1,2,24,3,4,5],[4,5],[]),([16,0,1,2,7,5,10],[1,6],[0]),([0,1,2,3,7,8,10],[],[0,1]),([26,0,1,2,3,4,5],[],[]),([28,0,1,2,3,4,5],[],[]),([0,1,2,3,12,13,10],[3],[0,1]),([22,0,1,2,4,7,13],[0,2,6],[]),([0,1,2,7,13,10],[3,5],[0,1]),([17,0,2,3,4,5,13],[7,8],[0]),([0,2,3,4,5,29],[9,10,11],[]),([30,0,1,2,3,4,5],[],[]),([31,0,1,2,3,4,5],[],[]),([16,0,1,2,4,5,32],[2,3,12],[0]),([20,0,1,2,6,4,13],[0],[]),([0,1,6,4,12,5,13],[3,13,14],[0]),([16,0,1,2,4,13,10],[0,2,6],[]),([22,0,1,2,6,4,5],[2,15],[]),([0,1,2,3,4,33,5],[],[]),([20,0,1,2,3,4,8],[15],[0]),([16,0,2,3,4,15,10],[0,2,16],[0]),([0,1,2,3,4,5,34],[2,5,17,18],[]),([0,1,2,4,19,5,13],[0],[0]),([0,1,2,3,4,9,5],[0,1],[0]),([0,2,3,4,15,10,32],[2,19],[]),([0,2,3,7,15,10],[3,5],[0]),([0,1,2,6,4,5,32],[2,15,20],[]),([20,0,1,3,4,12,5],[1],[]),([17,0,2,3,4,5,35],[7],[]),([0,3,6,4,15,8],[2,3,5,21,22],[0]),([22,0,1,2,3,7,10],[0,1],[]),([0,1,2,3,4,21,10],[1,2],[0,1]),([0,2,3,4,15,8,21],[2,23],[]),([14,0,2,3,4,15,8],[0,22,24],[0]),([14,0,1,3,4,12,5],[],[0]),([14,0,1,6,4,5,8],[6],[0]),([2,3,36,15,10],[2,5,25],[]),([20,0,1,3,6,4,8],[0],[]),([0,1,2,3,4,37,5],[4,5],[]),([17,0,2,3,38,4,5],[7],[]),([0,1,2,6,4,13,10],[2],[0]),([0,1,6,4,7,5,8],[2,5],[0]),([0,1,2,6,7,5,10],[5],[0]),([22,0,1,2,3,4,32],[2,12],[0]),([0,1,2,3,11,4,5],[2,4,5,26],[0,1]),([20,0,1,2,4,7,5],[1,2],[]),([14,0,1,2,4,5,21],[3,12],[0]),([20,0,1,2,3,4,21],[3,12],[0]),([22,0,1,2,3,4,10],[1,2],[0]),([14,0,1,2,3,4,10],[1,2],[0]),([39,0,1,2,3,4,5],[4,5],[]),([0,1,2,4,7,5,21],[1,2],[0]),([14,0,1,2,6,4,5],[15],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_6 : checkNodesBT W_46 g_46 F_46 P_46_6 A_46 B_46_5 6 N_46_6 = true := by decide +kernel
def B_46_6 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_6
set_option maxRecDepth 500000 in
lemma B_46_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 6 xs.toFinset) B_46_6 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_5_ok C_46_6
def P_46_7 : BT (Option BoundPool) := buildPoolsSubBT 7 W_46 r_46 S_46 ps_46 [0,1,2,3,4,5,6,7,8,10,11,14,15,17,18,19,20,22,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75]
def N_46_7 : List NodeSpec := [([16,0,1,2,3,4,5,10],[0,1,2,27],[0]),([16,0,1,2,3,4,5],[2,3,5,18,26,28],[0]),([22,0,1,2,3,4,7,5],[0,1,2,6],[0]),([0,1,2,3,4,7,5,8],[2,5],[0,1]),([40,0,2,3,6,4,5],[2,11,29,30,31],[]),([0,1,2,3,4,8,10],[2,11,32],[0,1]),([17,0,2,3,4,5],[7,8,10,11,33],[0]),([40,41,2,3,4,5],[31,34,35,36,37,38],[]),([0,2,3,6,4,5,15],[2,3,5,22],[0]),([42,0,2,3,4,5,15],[3,5,22,39],[]),([0,1,2,3,4,43,5,35],[2,3,40,41],[]),([42,0,1,2,3,4,5],[5,15,26,42,43,44],[]),([0,2,3,4,15,8],[2,5,45],[0]),([0,1,2,3,4,7,5,32],[2,46],[0]),([2,3,4,36,5,15],[2,5,47,48],[0]),([22,0,1,2,3,4,5],[2,3,4,5,26,49],[0]),([40,0,2,3,4,7,5],[2,11,37,50,51],[]),([0,2,3,4,7,5,15],[2,5,48],[0]),([40,2,3,4,36,5],[2,37,52,53,54],[]),([0,1,2,44,3,4,5,13],[5,31,55,56,57],[1]),([0,1,2,3,4,43,5,13],[3,5,11,40,56,58],[1]),([0,2,3,4,15,10],[2,5,19,48],[0]),([0,1,2,6,4,5,13],[2,3,5,14,20,59],[0,1]),([0,1,2,6,4,7,5],[2,5,11,20,60,61],[0,1]),([0,1,2,3,6,4,19,5],[5,62],[1]),([0,1,2,4,7,5,13],[2,5,63],[0,1]),([0,1,2,3,4,19,5],[2,5,11,17,64,65],[0,1]),([20,0,1,2,3,4,5],[2,3,4,5,26,66],[0]),([0,1,2,3,4,7,19,5],[5,67],[1]),([0,1,2,3,4,5,10,27],[5,68],[1]),([0,1,2,3,4,13,10],[2,3,5,63],[0]),([20,0,1,2,3,6,4,5],[0,6,15,66,69],[0]),([0,1,2,3,6,4,5,10],[2,5],[0,1]),([0,1,2,3,4,12,5,13],[3,6,11,56,59,70,71],[0,1]),([0,1,2,3,4,5,27],[2,4,5,11,17,72,73],[0,1]),([14,0,1,2,3,4,5],[2,3,5,18,26,74],[0,1]),([14,0,1,2,3,4,5,8],[0,6,15,74,75],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_7 : checkNodesBT W_46 g_46 F_46 P_46_7 A_46 B_46_6 7 N_46_7 = true := by decide +kernel
def B_46_7 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_7
set_option maxRecDepth 500000 in
lemma B_46_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 7 xs.toFinset) B_46_7 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_6_ok C_46_7
def P_46_8 : BT (Option BoundPool) := buildPoolsSubBT 7 W_46 r_46 S_46 ps_46 [0,1,2,4,5,6,11,12,15,22,26,29,31,34,39,40,42,46,52,55,57,68,70,71,73,76,77,78,79,80]
def N_46_8 : List NodeSpec := [([0,1,2,3,4,5,10],[0,1,2,5,11,68,76],[0,1]),([0,1,2,3,6,4,5],[2,5,6,15,29,31,77],[0,1]),([0,1,2,3,4,12,5],[1,2,4,5,11,31,70,71,73],[0,1]),([40,0,2,3,4,5],[0,2,4,11,31,34,42],[0]),([0,1,2,3,4,36,5],[1,2,5,26,31,52],[1]),([0,1,2,3,4,7,5],[1,2,5,6,11,42,46],[0,1]),([0,1,2,44,3,4,5],[4,5,11,15,31,55,57,78],[0]),([0,1,2,3,4,43,5],[1,2,4,5,11,31,40,42,79],[0]),([0,1,2,45,3,4,5],[2,26,31,80],[]),([0,2,3,4,5,15],[0,2,4,5,22,39],[0,1]),([0,1,46,2,3,4,5],[2,12,26,31],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_8 : checkNodesBT W_46 g_46 F_46 P_46_8 A_46 B_46_7 8 N_46_8 = true := by decide +kernel
def B_46_8 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_8
set_option maxRecDepth 500000 in
lemma B_46_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 8 xs.toFinset) B_46_8 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_7_ok C_46_8
def P_46_9 : BT (Option BoundPool) := buildPoolsSubBT 7 W_46 r_46 S_46 ps_46 [0,1,4,6,12,15,17,26]
def N_46_9 : List NodeSpec := [([0,1,2,3,4,5],[0,1,4,6,12,15,17,26],[0,1])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_46_9 : checkNodesBT W_46 g_46 F_46 P_46_9 A_46 B_46_8 9 N_46_9 = true := by decide +kernel
def B_46_9 : BT (List (List Nat)) := buildBucketsBT W_46 N_46_9
set_option maxRecDepth 500000 in
lemma B_46_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_46 9 xs.toFinset) B_46_9 :=
  buildBucketsBT_sound (by decide) gp_46 W_46_ok (buildPoolsSubBT_sound S_46_ok) A_46_ok B_46_8_ok C_46_9
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_46_ok : forestRootCheck r_46 g_46 [(VAR 0,8,9),(VAR 1,4,6),(VAR 2,2,6),(VAR 3,1,9),(VAR 4,2,18),(VAR 5,1,33)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_46_in : bucketContainsBT B_46_9 r_46 = true := by decide +kernel
lemma low_46 : Lower r_46 g_46 10 := lower_of_forestBT root_46_ok B_46_9_ok root_46_in
def g_47 := 0xfffffffffffefffefffeffeefffcf000fffffffffffefffefffeffeefffcf000
def r_47 : List Nat := varsOf 127
set_option maxHeartbeats 0 in
lemma low_47 : Lower r_47 g_47 11 := by
  have hc : Lower (varsOf 125) 0xfffffffffffafffafffaffaafff0f000fffffffffffafffafffaffaafff0f000 10 := carry_of (swaps := [(1,6),(3,4),(4,6),(5,6)]) (by decide +kernel) low_46
  exact lift_of_f (z := 2) (o := 0) (essPairs := [(VAR 1,16,18)]) (by decide +kernel) hc
def g_48 := 0xfffffffffffffffefffcfffcfefcaa00fffffffffffffffefffcfffcfefcaa00
def r_48 : List Nat := varsOf 127
set_option maxHeartbeats 0 in
lemma low_48 : Lower r_48 g_48 11 := by
  have hc : Lower (varsOf 125) 0xfffffffffffffffafff0fff0faf0aa00fffffffffffffffafff0fff0faf0aa00 10 := carry_of (swaps := [(1,6),(2,3),(3,4),(4,6),(5,6)]) (by decide +kernel) low_34
  exact lift_of_f (z := 2) (o := 0) (essPairs := [(VAR 1,16,18)]) (by decide +kernel) hc
def g_49 := 0xfffefffefffceac0fffefffefffceac0fffefffefffceac0fffefffefffceac0
def r_49 : List Nat := varsOf 63
set_option maxHeartbeats 0 in
lemma low_49 : Lower r_49 g_49 9 := by
  have hc : Lower (varsOf 47) 0xfffefffeeac0eac0fffefffeeac0eac0fffefffeeac0eac0fffefffeeac0eac0 8 := carry_of (swaps := [(4,5)]) (by decide +kernel) low_2
  exact lift_of_f (z := 16) (o := 0) (essPairs := [(VAR 4,2,18)]) (by decide +kernel) hc
def g_50 := 0xfffffffffffefffafffffcfcffccf000fffffffffffefffafffffcfcffccf000
def r_50 : List Nat := varsOf 127
set_option maxHeartbeats 0 in
lemma low_50 : Lower r_50 g_50 10 := by
  have hc : Lower (varsOf 126) 0xfffffffffffcfff0fffffcfcffccf000fffffffffffcfff0fffffcfcffccf000 9 := carry_of (swaps := [(0,6),(1,6),(2,6),(3,4)]) (by decide +kernel) low_49
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,64,65)]) (by decide +kernel) hc
def g_51 := 0xffffffffffeeffeefffffff0ffeac0c0ffffffffffeeffeefffffff0ffeac0c0
def r_51 : List Nat := varsOf 127
set_option maxHeartbeats 0 in
lemma low_51 : Lower r_51 g_51 10 := by
  have hc : Lower (varsOf 126) 0xffffffffffccffccfffffff0ffc0c0c0ffffffffffccffccfffffff0ffc0c0c0 9 := carry_of (swaps := [(0,6),(1,3),(2,3),(3,4),(4,6)]) (by decide +kernel) low_20
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,16,17)]) (by decide +kernel) hc
def g_52 := 0xffffffffffffffccfffaffeafff0c0c0ffffffffffffffccfffaffeafff0c0c0
def r_52 : List Nat := varsOf 127
set_option maxHeartbeats 0 in
lemma low_52 : Lower r_52 g_52 10 := by
  have hc : Lower (varsOf 126) 0xffffffffffffffccfff0ffc0fff0c0c0ffffffffffffffccfff0ffc0fff0c0c0 9 := carry_of (swaps := [(0,6),(2,3),(3,4),(5,6)]) (by decide +kernel) low_20
  exact lift_of_f (z := 1) (o := 0) (essPairs := [(VAR 0,32,33)]) (by decide +kernel) hc
def g_53 := 0xfffffffffffefffefffffffffffefffefffefffefffefffafefefefceeeeaa00
def r_53 : List Nat := varsOf 255
def p_53 : List Nat := [9,9,11,11,13,13,15,15,17,17,18,18,19,21,21,22,22,23,25,26,26,29,30,30,34,34,35,35,36,36,37,37,38,39,41,41,42,42,44,44,46,49,49,50,52,52,57,58,60,60,65,65,67,67,68,68,69,70,70,71,72,72,74,74,76,78,81,82,82,84,84,88,88,92,97,97,98,98,100,104,104,113,114,116,120,120,129,129,130,130,131,132,132,133,134,135,136,136,138,140,142,145,146,148,148,152,152,156,160,160,161,168,176,176,184,193,194,194,196,200,209,210,212,216,224,224,240,240]
def q_53 : List Nat := [8,1,10,3,12,5,14,7,16,1,16,2,3,20,5,20,6,7,24,24,10,28,28,14,32,2,33,3,32,4,33,5,6,7,40,33,40,10,40,12,14,48,33,48,48,20,56,56,56,28,64,1,66,3,64,4,5,66,6,7,64,8,66,10,12,14,80,80,66,80,20,80,24,28,96,33,96,66,96,96,40,112,112,112,112,56,128,1,128,2,3,128,4,5,6,7,128,8,10,12,14,144,144,144,20,144,24,28,128,32,33,40,144,48,56,192,192,66,192,192,208,208,208,208,192,96,208,112]
def F_53 : Nat := fullMask 128
set_option maxHeartbeats 0 in
lemma gp_53 : goodPairs g_53 p_53 q_53 := goodPairs_of (by decide +kernel)
def W_53 : BT Decor := buildWiresBT 5 (mkBase p_53 q_53 r_53) [(1,0,1),(2,8,5),(1,8,5),(3,4,10),(1,0,5),(3,1,12),(2,8,4),(3,0,10),(1,14,5),(3,1,16),(3,0,16),(2,14,5),(3,19,8),(1,1,5),(2,11,1),(2,11,0)]
lemma W_53_ok : btAll (fun x => faithful p_53 q_53 x ∧ x.1 < 2^256) W_53 := buildWiresBT_faithful (mkBase_ok (by decide))
def al_53 : List (List (Nat × Nat)) := [[]]
def A_53 : BT (List (Nat × Nat)) := btOfList 1 al_53
set_option maxHeartbeats 0 in
lemma A_53_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw g_53 = g_53) A_53 := btAll_ofList (autos_of (by decide +kernel))
set_option maxHeartbeats 0 in
lemma sl_53_0 : Slice r_53 g_53 (subcubeFast 4 0) 11 := by
  have hc : Lower (varsOf 251) 0xffffffffffeeffeeffffffffffeeffeeffeeffeeffeeffaaeeeeeecceeeeaa00 11 := carry_of (swaps := [(0,6),(1,5),(2,7),(4,6),(5,7),(6,7)]) (by decide +kernel) low_11
  exact slice_fast_direct_f (z := 4) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_53_1 : Slice r_53 g_53 (subcubeFast 16 0) 11 := by
  have hc : Lower (varsOf 239) 0xfffffffffffefffefffffffffffefffefffefffefffafffafefcfefcaa00aa00 11 := carry_of (swaps := [(0,2),(1,2),(4,7),(5,7),(6,7)]) (by decide +kernel) low_12
  exact slice_fast_direct_f (z := 16) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_53_2 : Slice r_53 g_53 (subcubeFast 64 0) 11 := by
  have hc : Lower (varsOf 191) 0xfffffffffffefffefffffffffffefffefefefefceeeeaa00fefefefceeeeaa00 11 := carry_of (swaps := [(0,5),(1,3),(2,3),(3,5),(4,5),(6,7)]) (by decide +kernel) low_32
  exact slice_fast_direct_f (z := 64) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_53_3 : Slice r_53 g_53 (subcubeFast 8 0) 11 := by
  have hc : Lower (varsOf 247) 0xfffffffffefefefefffffffffefefefefefefefefefefafafefefcfceeee0000 11 := carry_of (swaps := [(0,5),(1,4),(2,3),(3,7),(4,5),(5,7),(6,7)]) (by decide +kernel) low_40
  exact slice_fast_direct_f (z := 8) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_53_4 : Slice r_53 g_53 (subcubeFast 128 0) 11 := by
  have hc : Lower (varsOf 127) 0xfffefffefffefffafefefefceeeeaa00fffefffefffefffafefefefceeeeaa00 11 := carry_of (swaps := [(0,5),(1,3),(2,3),(3,5),(4,5)]) (by decide +kernel) low_44
  exact slice_fast_direct_f (z := 128) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_53_5 : Slice r_53 g_53 (identDom 4 5) 11 := by
  have hc : Lower (varsOf 223) 0xfffffffefffffffefffffffefffffffefffefffafffefffafefeaa00fefeaa00 11 := carry_of (swaps := [(0,3),(1,3),(2,3),(4,5),(5,7),(6,7)]) (by decide +kernel) low_47
  exact slice_ident (u := 4) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_53_6 : Slice r_53 g_53 (identDom 0 5) 11 := by
  have hc : Lower (varsOf 223) 0xfffefffefffefffefffefffefffefffefffefffafffefffaeeeeaaa8eeeeaaa8 11 := carry_of (swaps := [(0,6),(1,3),(2,3),(4,6),(5,7)]) (by decide +kernel) low_48
  exact slice_ident (u := 0) (v := 5) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_53_7 : Slice r_53 g_53 (subcubeFast 2 0) 10 := by
  have hc : Lower (varsOf 253) 0xfffffffffffafffafffffffffffafffafffafffafffafffafafafaf0aaaaaa00 10 := carry_of (swaps := [(0,6),(1,7),(2,4),(3,4),(4,6),(5,7)]) (by decide +kernel) low_50
  exact slice_fast_direct_f (z := 2) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_53_8 : Slice r_53 g_53 (subcubeFast 32 0) 10 := by
  have hc : Lower (varsOf 223) 0xfffefffefffefffefffefffefffefffefffefffafffefffaeeeeaa00eeeeaa00 10 := carry_of (swaps := [(0,5),(2,5),(4,5),(5,7),(6,7)]) (by decide +kernel) low_51
  exact slice_fast_direct_f (z := 32) (o := 0) (by decide +kernel) hc
set_option maxHeartbeats 0 in
lemma sl_53_9 : Slice r_53 g_53 (subcubeFast 1 0) 10 := by
  have hc : Lower (varsOf 254) 0xfffffffffffcfffcfffffffffffcfffcfffcfffcfffcfff0fcfcfcfccccc0000 10 := carry_of (swaps := [(0,7),(1,5),(2,4),(3,5),(4,7),(6,7)]) (by decide +kernel) low_52
  exact slice_fast_direct_f (z := 1) (o := 0) (by decide +kernel) hc
def S_53 : BT (Option (Nat × Nat)) := btOfList 4 [some (subcubeFast 4 0,11),some (subcubeFast 16 0,11),some (subcubeFast 64 0,11),some (subcubeFast 8 0,11),some (subcubeFast 128 0,11),some (identDom 4 5,11),some (identDom 0 5,11),some (subcubeFast 2 0,10),some (subcubeFast 32 0,10),some (subcubeFast 1 0,10)]
lemma S_53_ok : btAll (fun o => ∀ p, o = some p → Slice r_53 g_53 p.1 p.2) S_53 := btAll_ofList (forall_cons (fun _ h => by cases h; exact sl_53_0) (forall_cons (fun _ h => by cases h; exact sl_53_1) (forall_cons (fun _ h => by cases h; exact sl_53_2) (forall_cons (fun _ h => by cases h; exact sl_53_3) (forall_cons (fun _ h => by cases h; exact sl_53_4) (forall_cons (fun _ h => by cases h; exact sl_53_5) (forall_cons (fun _ h => by cases h; exact sl_53_6) (forall_cons (fun _ h => by cases h; exact sl_53_7) (forall_cons (fun _ h => by cases h; exact sl_53_8) (forall_cons (fun _ h => by cases h; exact sl_53_9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
def ps_53 : BT (Option PoolSpec) := btOfList 8 ((([(7,[(1,0,21),(3,4,10)]),(6,[(1,1,12),(3,4,10)]),(0,[(1,0,1),(2,8,4)]),(6,[(1,0,1),(2,8,4),(3,0,10)]),(1,[(1,0,1),(2,14,5),(3,19,8)]),(5,[(1,0,1),(2,8,4),(3,19,8)]),(7,[(2,8,4),(2,14,5),(3,19,8)]),(8,[(1,0,1),(2,8,4),(3,19,8)]),(6,[(1,1,5),(3,4,10),(3,5,10)]),(8,[(1,0,21),(3,4,10)]),(5,[(1,0,1),(2,8,4),(1,14,5)]),(7,[(1,8,5),(3,0,10)]),(1,[(1,0,1),(1,8,5),(3,0,10),(3,1,10)]),(6,[(1,0,1),(3,0,10),(3,1,10)]),(1,[(1,0,1),(1,8,5),(3,1,10),(2,8,5)]),(9,[(2,8,4)]),(4,[(1,0,1),(1,8,5),(3,0,10),(3,1,10)]),(7,[(1,8,5),(3,5,10)]),(4,[(1,0,1),(1,8,5),(3,1,10),(3,5,10)]),(6,[(1,0,1),(2,8,4)]),(7,[(1,0,21),(3,5,10)]),(6,[(1,1,5),(3,1,10),(3,5,10)]),(9,[(2,8,4),(2,14,5)]),(7,[(2,8,4)]),(6,[(1,0,1),(3,1,12),(2,8,5)]),(5,[(1,0,1),(1,8,5),(3,5,10)]),(6,[(1,0,1),(2,8,4),(3,5,10)]),(0,[(1,0,1),(1,8,5),(3,4,10)]),(6,[(1,0,1),(3,0,10),(3,4,10)]),(9,[(1,8,5),(3,4,10)]),(6,[(1,0,1),(3,1,10),(3,5,10)]),(1,[(1,0,1),(1,8,5),(3,1,10),(3,5,10)]),(7,[(1,8,5),(3,4,10)]),(6,[(1,0,1),(3,4,10),(3,5,10)]),(1,[(1,0,1)]),(5,[(1,0,1),(2,8,4)]),(1,[(1,0,1),(1,8,5)]),(7,[(1,0,21)]),(6,[(1,1,5),(3,5,10)]),(8,[(1,0,21)]),(1,[(1,1,5),(1,0,21),(3,5,10)]),(0,[(1,0,1),(1,8,5),(3,1,10)]),(6,[(1,0,1),(3,1,10)]),(7,[(1,8,5)]),(4,[(1,0,1),(1,8,5),(3,1,10)]),(9,[(1,8,5),(3,1,10)]),(1,[(1,0,1),(1,8,5),(3,1,10)]),(8,[(1,0,1),(3,1,10)]),(6,[(1,0,1),(3,1,12)]),(0,[(1,0,1),(1,0,5),(3,1,12)]),(3,[(1,0,1),(1,0,5),(3,1,12)]),(1,[(1,0,1),(1,0,5),(3,1,12)]),(7,[(1,0,5)]),(2,[(1,0,1),(1,0,5),(3,1,12)]),(4,[(1,0,1),(1,0,5),(3,1,12)]),(1,[(1,0,1),(2,8,5)]),(7,[(2,8,4),(2,8,5)]),(8,[(1,0,1),(2,8,4)]),(0,[(1,0,1),(2,8,4),(2,8,5)]),(3,[(1,0,1),(2,8,4)]),(3,[(1,0,1),(2,8,4),(2,8,5)]),(2,[(1,0,1),(2,8,4)]),(2,[(1,0,1),(2,8,4),(2,8,5)]),(4,[(1,0,1),(2,8,4)]),(4,[(1,0,1),(2,8,4),(2,8,5)]),(9,[(2,8,4),(2,8,5)]),(5,[(1,0,1),(2,8,4),(1,8,5)]),(5,[]),(5,[(1,0,1),(1,8,5)]),(4,[(1,0,1),(2,8,4),(1,8,5)]),(9,[(2,8,4),(1,8,5)]),(0,[(1,0,1),(2,8,4),(1,8,5)]),(7,[(2,8,4),(1,8,5)]),(3,[(1,0,1),(2,8,4),(1,8,5)]),(2,[(1,0,1),(2,8,4),(1,8,5)]),(6,[(1,1,5),(3,1,10)]),(1,[(1,1,5),(1,0,21),(3,1,10)]),(0,[(1,1,5),(1,0,21),(3,1,10)]),(7,[]),(4,[(1,1,5),(1,0,21),(3,1,10)]),(9,[(1,1,5),(3,1,10)]),(1,[(1,0,1),(2,14,5)]),(1,[(1,1,5)]),(6,[(1,1,5),(3,4,10)]),(0,[]),(0,[(1,0,1),(1,8,5),(3,0,10)]),(4,[(1,0,1),(1,8,5),(3,0,10)]),(8,[(1,0,1),(3,0,10)]),(1,[(1,0,1),(1,8,5),(3,0,10)]),(6,[(1,0,1),(3,0,10)]),(1,[(1,0,1),(1,14,5)]),(7,[(2,8,4),(1,14,5)]),(0,[(1,0,1),(2,8,4),(1,14,5)]),(3,[(1,0,1),(2,8,4),(1,14,5)]),(2,[(1,0,1),(2,8,4),(1,14,5)]),(4,[(1,0,1),(2,8,4),(1,14,5)]),(9,[(2,8,4),(1,14,5)]),(6,[]),(6,[(1,1,12),(3,5,10)]),(7,[(1,0,5),(3,5,10)]),(3,[(1,0,5),(1,1,12),(3,5,10)]),(1,[(1,0,5),(1,1,12),(3,5,10)]),(2,[(1,0,5),(1,1,12),(3,5,10)]),(4,[(1,0,5),(1,1,12),(3,5,10)]),(0,[(1,0,5),(1,1,12),(3,5,10)]),(6,[(1,1,12)]),(7,[(2,8,4),(2,14,5)]),(0,[(1,0,1),(2,8,4),(2,14,5)]),(3,[(1,0,1),(2,8,4),(2,14,5)]),(2,[(1,0,1),(2,8,4),(2,14,5)]),(4,[(1,0,1),(2,8,4),(2,14,5)]),(6,[(1,0,1),(2,8,5)]),(7,[(1,0,5),(2,8,5)]),(3,[(1,0,1),(1,0,5),(2,8,5)]),(1,[(1,0,1),(1,0,5),(2,8,5)]),(2,[(1,0,1),(1,0,5),(2,8,5)]),(4,[(1,0,1),(1,0,5),(2,8,5)]),(9,[(2,8,5)]),(0,[(1,0,1),(1,0,5),(2,8,5)]),(6,[(1,1,5)]),(7,[(1,0,21),(3,0,21)]),(8,[(1,0,21),(3,0,21)]),(6,[(1,1,5),(3,0,21)]),(1,[(1,0,1),(1,0,5)]),(5,[(1,0,1),(1,0,5),(2,8,4)]),(4,[(1,0,1),(1,0,5),(2,8,4)]),(0,[(1,0,1),(1,0,5),(2,8,4)]),(3,[(1,0,1),(1,0,5),(2,8,4)]),(7,[(1,0,5),(2,8,4)]),(2,[(1,0,1),(1,0,5),(2,8,4)]),(0,[(1,0,5),(1,1,12),(3,0,10)]),(6,[(1,1,12),(3,0,10)]),(4,[(1,0,5),(1,1,12),(3,0,10)]),(7,[(1,0,5),(3,0,10)]),(8,[(1,1,12),(3,0,10)]),(3,[(1,0,5),(1,1,12),(3,0,10)]),(1,[(1,0,5),(1,1,12),(3,0,10)]),(2,[(1,0,5),(1,1,12),(3,0,10)]),(3,[(1,0,1),(1,8,5),(3,4,10)]),(8,[(1,0,1),(3,4,10)]),(2,[(1,0,1),(1,8,5),(3,4,10)]),(4,[(1,0,1),(1,8,5),(3,4,10)]),(6,[(1,0,1),(3,5,10)]),(1,[(1,0,1),(1,8,5),(3,5,10)]),(4,[(1,0,1),(1,8,5),(3,5,10)]),(0,[(1,0,1),(1,8,5),(3,5,10)]),(9,[(1,8,5)]),(3,[(1,0,1),(1,8,5),(3,0,10)]),(2,[(1,0,1),(1,8,5),(3,0,10)]),(6,[(1,0,1),(3,4,10)]),(1,[(1,0,5)]),(7,[(1,0,5),(3,4,10)]),(1,[(1,1,5),(1,0,21)]),(4,[(1,1,5),(1,0,21),(3,4,10)]),(9,[(1,1,5),(3,4,10)]),(0,[(1,1,5),(1,0,21),(3,4,10)]),(3,[(1,1,5),(1,0,21),(3,4,10)]),(2,[(1,1,5),(1,0,21),(3,4,10)]),(6,[(1,1,12),(3,1,12)]),(3,[(1,0,1),(1,8,5),(3,1,10)]),(2,[(1,0,1),(1,8,5),(3,1,10)]),(5,[(1,0,1)]),(6,[(1,0,1)]),(7,[(1,8,5),(2,8,5)]),(1,[(1,0,1),(1,8,5),(2,8,5)]),(5,[(1,0,1),(1,8,5),(3,4,10)]),(4,[(1,1,5),(1,0,21),(3,5,10)]),(0,[(1,1,5),(1,0,21),(3,5,10)]),(1,[(1,0,5),(1,1,12)]),(4,[(1,0,5),(1,1,12),(3,4,10)]),(0,[(1,0,5),(1,1,12),(3,4,10)]),(3,[(1,0,5),(1,1,12),(3,4,10)]),(2,[(1,0,5),(1,1,12),(3,4,10)]),(6,[(3,1,12)]),(0,[(1,0,5)]),(0,[(1,0,5),(3,1,12)]),(3,[(1,0,5)]),(3,[(1,0,5),(3,1,12)]),(1,[(1,0,5),(3,1,12)]),(2,[(1,0,5)]),(2,[(1,0,5),(3,1,12)]),(4,[(1,0,5)]),(4,[(1,0,5),(3,1,12)]),(9,[(3,1,12)]),(8,[(3,1,12)]),(3,[]),(1,[]),(2,[]),(4,[]),(0,[(1,0,5),(1,1,12)]),(9,[(1,1,12)]),(4,[(1,0,5),(1,1,12)]),(8,[(1,1,12)]),(3,[(1,0,5),(1,1,12)]),(2,[(1,0,5),(1,1,12)]),(9,[(1,1,5)]),(4,[(1,1,5),(1,0,21)]),(0,[(1,1,5),(1,0,21)]),(3,[(1,1,5),(1,0,21)]),(2,[(1,1,5),(1,0,21)]),(7,[(2,8,5)]),(8,[(1,0,1)]),(0,[(1,0,1)]),(0,[(1,0,1),(2,8,5)]),(3,[(1,0,1)]),(3,[(1,0,1),(2,8,5)]),(2,[(1,0,1)]),(2,[(1,0,1),(2,8,5)]),(4,[(1,0,1)]),(4,[(1,0,1),(2,8,5)]),(0,[(1,1,5)]),(0,[(1,1,5),(3,0,21)]),(3,[(1,1,5)]),(3,[(1,1,5),(3,0,21)]),(1,[(1,1,5),(3,0,21)]),(2,[(1,1,5)]),(2,[(1,1,5),(3,0,21)]),(4,[(1,1,5)]),(4,[(1,1,5),(3,0,21)]),(7,[(3,0,21)]),(8,[(3,0,21)]),(0,[(1,0,1),(1,8,5)]),(3,[(1,0,1),(1,8,5)]),(4,[(1,0,1),(1,8,5)]),(2,[(1,0,1),(1,8,5)]),(9,[]),(0,[(1,0,1),(1,0,5)]),(3,[(1,0,1),(1,0,5)]),(2,[(1,0,1),(1,0,5)]),(4,[(1,0,1),(1,0,5)]),(8,[])] : List PoolSpec)).map some)
def B_53_6 : BT (List (List Nat)) := BT.empty
lemma B_53_6_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_53 6 xs.toFinset) B_53_6 := .empty
def P_53_7 : BT (Option BoundPool) := buildPoolsSubBT 8 W_53 r_53 S_53 ps_53 []
def N_53_7 : List NodeSpec := [([9,11,13,0,2,3,6,7],[],[]),([14,13,15,2,3,5,6,7],[],[]),([9,14,17,0,2,3,6,7],[],[]),([9,14,18,1,2,3,6,7],[],[]),([11,13,15,2,3,5,6,7],[],[]),([9,14,13,0,2,3,6,7],[],[]),([14,1,20,2,3,12,6,7],[],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_53_7 : checkNodesBT W_53 g_53 F_53 P_53_7 A_53 B_53_6 7 N_53_7 = true := by decide +kernel
def B_53_7 : BT (List (List Nat)) := buildBucketsBT W_53 N_53_7
set_option maxRecDepth 500000 in
lemma B_53_7_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_53 7 xs.toFinset) B_53_7 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok (buildPoolsSubBT_sound S_53_ok) A_53_ok B_53_6_ok C_53_7
def P_53_8 : BT (Option BoundPool) := buildPoolsSubBT 8 W_53 r_53 S_53 ps_53 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
def N_53_8 : List NodeSpec := [([11,13,0,2,3,5,21,6,7],[0],[0]),([13,15,2,3,4,5,21,6,7],[],[]),([9,11,0,1,2,3,12,6,7],[1],[0]),([9,13,0,2,3,4,12,6,7],[],[]),([11,15,1,2,3,5,12,6,7],[1],[0]),([14,15,1,2,3,5,10,6,7],[2,3],[0]),([14,0,1,20,2,3,5,6,7],[4,5,6,7],[0]),([9,11,0,1,2,3,21,6,7],[0,8,9],[]),([9,14,0,1,2,3,16,6,7],[10],[0]),([13,15,8,2,3,4,5,6,7],[11,12,13],[0]),([19,11,0,1,2,3,12,6,7],[1],[]),([9,13,0,8,2,3,4,6,7],[14],[0]),([14,17,0,8,2,3,5,6,7],[15],[0]),([13,15,2,3,4,5,6,7],[12,16],[]),([9,13,0,2,3,4,6,7],[17,18],[]),([9,14,1,8,2,3,12,6,7],[19],[]),([9,13,0,2,3,4,21,6,7],[20,21],[]),([19,14,0,1,2,3,16,6,7],[10],[]),([19,14,1,8,2,3,12,6,7],[22],[0]),([13,15,2,3,4,5,12,6,7],[],[]),([14,13,0,2,3,5,10,6,7],[2],[0]),([14,18,1,8,2,3,5,6,7],[23],[0]),([9,13,8,2,3,4,12,6,7],[24],[]),([14,13,8,2,3,5,12,6,7],[23],[]),([14,15,1,8,2,3,5,6,7],[3,23],[]),([14,13,0,8,2,3,5,6,7],[23],[0]),([13,15,2,3,4,5,10,6,7],[12,13],[0]),([19,11,0,1,2,3,21,6,7],[0],[]),([9,14,0,1,2,3,10,6,7],[2,25,26],[0]),([11,15,1,2,3,5,10,6,7],[27,28],[0]),([11,13,0,2,3,5,10,6,7],[27],[0]),([22,11,0,8,2,3,5,6,7],[29],[]),([9,13,0,2,3,4,10,6,7],[30,31],[0]),([11,15,1,8,2,3,5,6,7],[28,32],[]),([9,11,0,1,2,3,10,6,7],[27,33],[0]),([19,14,0,1,2,3,10,6,7],[34,35],[]),([19,11,0,1,2,3,10,6,7],[36],[]),([11,13,0,8,2,3,5,6,7],[32],[0]),([23,11,1,8,2,3,5,6,7],[32],[])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_53_8 : checkNodesBT W_53 g_53 F_53 P_53_8 A_53 B_53_7 8 N_53_8 = true := by decide +kernel
def B_53_8 : BT (List (List Nat)) := buildBucketsBT W_53 N_53_8
set_option maxRecDepth 500000 in
lemma B_53_8_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_53 8 xs.toFinset) B_53_8 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok (buildPoolsSubBT_sound S_53_ok) A_53_ok B_53_7_ok C_53_8
def P_53_9 : BT (Option BoundPool) := buildPoolsSubBT 8 W_53 r_53 S_53 ps_53 [0,1,2,9,10,11,15,17,19,20,22,23,27,29,32,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172]
def N_53_9 : List NodeSpec := [([9,0,1,2,3,4,21,10,6,7],[37,38,39,40],[0]),([13,0,2,3,4,5,10,6,7],[41,42,43,44,45,46,47],[0]),([13,8,2,3,4,5,12,6,7],[48,49,50,51,52,53,54],[0]),([13,0,8,2,3,4,5,10,6,7],[42,43,46],[0]),([9,14,0,1,8,2,3,5,6,7],[19,23,55,56,57],[0]),([9,14,0,1,2,3,5,6,7],[2,19,23,35,55,56,57,58,59,60,61,62,63,64,65],[0]),([14,0,1,2,3,5,10,6,7],[35,57,59,61,66,67,68,69,70,71,72,73,74],[0]),([13,0,2,3,4,5,21,10,6,7],[37,75,76],[0]),([13,0,2,3,4,5,21,6,7],[37,75,76,77,78,79,80],[0]),([19,14,0,1,8,2,3,5,6,7],[19,22,23,35,57,81],[0]),([11,0,1,2,3,5,21,10,6,7],[0,9,82,83],[0]),([15,1,2,3,4,5,10,6,7],[11,84,85,86,87,88,89],[0]),([14,0,1,2,3,5,16,6,7],[10,57,90,91,92,93,94,95,96],[0]),([9,0,1,2,3,4,12,6,7],[97,98,99,100,101,102,103,104],[0]),([14,0,1,8,2,3,5,16,6,7],[10,57,90,96],[0]),([9,0,1,2,3,4,12,10,6,7],[98,99,101,105],[0]),([19,14,0,1,2,3,5,6,7],[2,19,22,23,35,57,59,61,63,106,107,108,109,110],[0]),([9,1,8,2,3,4,12,6,7],[111,112,113,114,115,116,117,118],[0]),([15,1,2,3,4,5,21,10,6,7],[119,120,121,122],[0]),([14,1,8,2,3,5,12,6,7],[15,23,57,123,124,125,126,127,128,129],[0]),([15,1,2,3,4,5,12,6,7],[97,130,131,132,133,134,135,136,137],[0]),([11,0,1,2,3,5,6,7],[27,29,32,36,138,139,140,141],[]),([9,0,1,2,3,4,10,6,7],[17,142,143,144,145],[0]),([11,0,1,2,3,5,10,6,7],[27,29,32,36,138,139,140,141],[0]),([15,1,8,2,3,4,5,6,7],[11,78,85,86,87,88,89,146,147,148],[0]),([11,0,1,8,2,3,5,10,6,7],[32,36,149],[0]),([11,0,1,2,3,5,12,10,6,7],[1,150,151],[0]),([15,1,8,2,3,4,5,10,6,7],[43,88,89],[0]),([11,0,1,2,3,5,21,6,7],[0,9,83,152,153,154,155,156,157],[0]),([13,0,2,3,4,5,12,10,6,7],[52,158],[0]),([13,0,8,2,3,4,5,6,7],[41,42,43,44,46,47,78,159,160],[0]),([14,0,1,8,2,3,5,10,6,7],[19,36,72,161],[0]),([9,0,1,8,2,3,4,10,6,7],[111,162,163,164],[0]),([11,0,1,8,2,3,5,6,7],[27,29,32,36,138,139,140,141,165],[0]),([15,1,2,3,4,5,12,10,6,7],[105,131,133,136],[0]),([9,0,1,2,3,4,21,6,7],[20,38,39,40,78,166,167],[]),([11,0,1,2,3,5,12,6,7],[1,151,168,169,170,171,172],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_53_9 : checkNodesBT W_53 g_53 F_53 P_53_9 A_53 B_53_8 9 N_53_9 = true := by decide +kernel
def B_53_9 : BT (List (List Nat)) := buildBucketsBT W_53 N_53_9
set_option maxRecDepth 500000 in
lemma B_53_9_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_53 9 xs.toFinset) B_53_9 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok (buildPoolsSubBT_sound S_53_ok) A_53_ok B_53_8_ok C_53_9
def P_53_10 : BT (Option BoundPool) := buildPoolsSubBT 8 W_53 r_53 S_53 ps_53 [2,15,23,34,35,36,37,39,43,52,55,57,59,61,63,78,82,84,97,105,111,117,119,122,123,146,150,152,162,168,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229]
def N_53_10 : List NodeSpec := [([13,0,1,2,3,4,5,12,6,7],[52,150,173,174,175,176,177,178,179,180,181,182,183,184],[0]),([13,0,1,2,3,4,5,6,7],[52,78,84,173,175,177,178,180,182,183,184,185,186,187,188],[0]),([0,1,2,3,4,5,12,10,6,7],[52,105,168,189,190,191,192,193,194],[0]),([0,1,2,3,4,5,21,10,6,7],[37,39,119,152,195,196,197,198,199],[0]),([9,0,1,8,2,3,4,5,6,7],[34,55,78,111,117,162,200,201,202,203,204,205,206,207,208,209],[0]),([15,0,1,2,3,4,5,21,6,7],[78,82,119,195,210,211,212,213,214,215,216,217,218,219,220],[0]),([0,1,2,3,4,5,10,6,7],[36,43,146,162,187,201,221,222,223,224],[0]),([15,0,1,2,3,4,5,6,7],[78,84,97,122,185,186,187,188,195,211,213,214,216,218,219,220],[0]),([0,1,8,2,3,4,5,10,6,7],[36,43,146,201,221,222,223,224],[0]),([14,0,1,8,2,3,5,6,7],[2,15,23,34,35,57,59,61,63],[0]),([14,0,1,2,3,5,6,7],[2,15,23,34,35,57,59,61,63],[0]),([9,0,1,2,3,4,5,6,7],[55,78,84,97,111,117,185,186,187,188,200,201,203,205,207,209],[0]),([1,8,2,3,4,5,12,6,7],[52,123,201,225,226,227,228,229],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_53_10 : checkNodesBT W_53 g_53 F_53 P_53_10 A_53 B_53_9 10 N_53_10 = true := by decide +kernel
def B_53_10 : BT (List (List Nat)) := buildBucketsBT W_53 N_53_10
set_option maxRecDepth 500000 in
lemma B_53_10_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_53 10 xs.toFinset) B_53_10 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok (buildPoolsSubBT_sound S_53_ok) A_53_ok B_53_9_ok C_53_10
def P_53_11 : BT (Option BoundPool) := buildPoolsSubBT 8 W_53 r_53 S_53 ps_53 [34,52,78,82,97,150,174,176,179,181,195,201,202,204,206,208,210,212,215,217,225,230]
def N_53_11 : List NodeSpec := [([0,1,2,3,4,5,21,6,7],[78,82,97,195,210,212,215,217,230],[0]),([0,1,2,3,4,5,12,6,7],[52,97,150,174,176,179,181,225,230],[0]),([0,1,8,2,3,4,5,6,7],[34,78,201,202,204,206,208,225],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_53_11 : checkNodesBT W_53 g_53 F_53 P_53_11 A_53 B_53_10 11 N_53_11 = true := by decide +kernel
def B_53_11 : BT (List (List Nat)) := buildBucketsBT W_53 N_53_11
set_option maxRecDepth 500000 in
lemma B_53_11_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_53 11 xs.toFinset) B_53_11 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok (buildPoolsSubBT_sound S_53_ok) A_53_ok B_53_10_ok C_53_11
def P_53_12 : BT (Option BoundPool) := buildPoolsSubBT 8 W_53 r_53 S_53 ps_53 [78,84,97,185,186,187,188,225,230]
def N_53_12 : List NodeSpec := [([0,1,2,3,4,5,6,7],[78,84,97,185,186,187,188,225,230],[0])]
set_option maxRecDepth 200000 in set_option maxHeartbeats 0 in
lemma C_53_12 : checkNodesBT W_53 g_53 F_53 P_53_12 A_53 B_53_11 12 N_53_12 = true := by decide +kernel
def B_53_12 : BT (List (List Nat)) := buildBucketsBT W_53 N_53_12
set_option maxRecDepth 500000 in
lemma B_53_12_ok : btAll (fun (bk : List (List Nat)) => ∀ xs ∈ bk, Impossible g_53 12 xs.toFinset) B_53_12 :=
  buildBucketsBT_sound (by decide) gp_53 W_53_ok (buildPoolsSubBT_sound S_53_ok) A_53_ok B_53_11_ok C_53_12
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_53_ok : forestRootCheck r_53 g_53 [(VAR 0,8,9),(VAR 1,16,18),(VAR 2,32,36),(VAR 3,1,9),(VAR 4,1,17),(VAR 5,2,34),(VAR 6,1,65),(VAR 7,1,129)] = true := by decide +kernel
set_option maxRecDepth 500000 in set_option maxHeartbeats 0 in
lemma root_53_in : bucketContainsBT B_53_12 r_53 = true := by decide +kernel
lemma low_53 : Lower r_53 g_53 13 := lower_of_forestBT root_53_ok B_53_12_ok root_53_in

def targetFn (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def temoin : List Gate := [⟨.or,[6,7]⟩,⟨.or,[3,6]⟩,⟨.or,[4,7]⟩,⟨.or,[2,1]⟩,⟨.or,[11,7]⟩,⟨.or,[3,2]⟩,⟨.or,[9,10]⟩,⟨.and,[1,10]⟩,⟨.and,[12,5]⟩,⟨.or,[0,15]⟩,⟨.and,[14,17]⟩,⟨.and,[13,8]⟩,⟨.or,[19,16]⟩,⟨.or,[20,18]⟩]
lemma temoin_ok : ∀ g ∈ temoin, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by simp [temoin]
set_option maxHeartbeats 0 in
lemma edge_eq_G : ∀ r : Row, targetFn (evalInput r) = g_53.testBit r.val := by decide +kernel
set_option maxHeartbeats 0 in
lemma temoin_eval : ∀ r : Row, Circuit.eval ⟨temoin, 21⟩ (List.ofFn (evalInput r)) = g_53.testBit r.val := by decide +kernel

end PEqualNP.Outside.L_meta_30124

open PEqualNP.Outside.L_meta_30124 in
theorem PEqualNP.Outside.L_meta_30124 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o legal _ spec
  exact replace_of_lower g_53 (by decide) (by decide) (by decide) 13 low_53 temoin 21 (by decide) temoin_ok targetFn edge_eq_G temoin_eval gates o legal spec
