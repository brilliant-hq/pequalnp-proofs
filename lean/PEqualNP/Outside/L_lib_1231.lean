import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1231

/-! ### Part 1: Finite C6 NOT-gadget and 7-vertex SWITCH-gadget (exact mod-2 counts by `decide`) -/

private def c6Adj (a b : Fin 6) : Bool :=
  (a.val == 0 && (b.val == 3 || b.val == 4)) ||
  (a.val == 1 && (b.val == 3 || b.val == 5)) ||
  (a.val == 2 && (b.val == 4 || b.val == 5)) ||
  (a.val == 3 && (b.val == 0 || b.val == 1)) ||
  (a.val == 4 && (b.val == 0 || b.val == 2)) ||
  (a.val == 5 && (b.val == 1 || b.val == 2))

private def c6Shore (a : Fin 6) : Bool := decide (3 ≤ a.val)

private lemma c6Adj_irrefl : ∀ a : Fin 6, c6Adj a a = false := by decide
private lemma c6Adj_symm : ∀ a b : Fin 6, c6Adj a b = c6Adj b a := by decide
private lemma c6Adj_bip : ∀ a b : Fin 6, c6Adj a b = true → c6Shore a ≠ c6Shore b := by decide

-- Internal choices for vertices {2, 3, 4, 5} of the C6 NOT-gadget given (b0, b1) for vertices (0, 1)
private def notValid (b0 b1 : Bool) (c : Fin 4 → Bool) : Bool :=
  let v : Fin 6 → Bool := fun k =>
    match k.val with
    | 0 => b0
    | 1 => b1
    | 2 => c 0
    | 3 => c 1
    | 4 => c 2
    | _ => c 3
  !(v 0 && v 3) && !(v 0 && v 4) && !(v 1 && v 3) &&
  !(v 1 && v 5) && !(v 2 && v 4) && !(v 2 && v 5)

private def notBit (b0 b1 : Bool) (c : Fin 4 → Bool) (k : Fin 6) : Bool :=
  match k.val with
  | 0 => b0
  | 1 => b1
  | 2 => c 0
  | 3 => c 1
  | 4 => c 2
  | _ => c 3

private lemma notValid_no_edge : ∀ (b0 b1 : Bool) (c : Fin 4 → Bool) (ka kb : Fin 6),
    notValid b0 b1 c = true → c6Adj ka kb = true →
    notBit b0 b1 c ka = true → notBit b0 b1 c kb = true → False := by decide

private def notCount (b0 b1 : Bool) : Nat :=
  ((Finset.univ : Finset (Fin 4 → Bool)).filter (fun c => notValid b0 b1 c = true)).card

private lemma notCount_mod2 : ∀ b0 b1 : Bool, notCount b0 b1 % 2 = if b1 = !b0 then 1 else 0 := by
  decide

private def swAdj (a b : Fin 7) : Bool :=
  (a.val == 0 && (b.val == 3 || b.val == 4)) ||
  (a.val == 1 && (b.val == 3 || b.val == 5 || b.val == 6)) ||
  (a.val == 2 && (b.val == 4 || b.val == 5)) ||
  (a.val == 3 && (b.val == 0 || b.val == 1)) ||
  (a.val == 4 && (b.val == 0 || b.val == 2)) ||
  (a.val == 5 && (b.val == 1 || b.val == 2)) ||
  (a.val == 6 && b.val == 1)

private def swShore (a : Fin 7) : Bool := decide (a.val < 3)

private lemma swAdj_irrefl : ∀ a : Fin 7, swAdj a a = false := by decide
private lemma swAdj_symm : ∀ a b : Fin 7, swAdj a b = swAdj b a := by decide
private lemma swAdj_bip : ∀ a b : Fin 7, swAdj a b = true → swShore a ≠ swShore b := by decide

private lemma swAdj_six : ∀ a b : Fin 7, swAdj a b = true → (a.val = 6 ∨ b.val = 6) →
    (a.val = 1 ∨ a.val = 6) ∧ (b.val = 1 ∨ b.val = 6) := by decide

-- Choices for all 7 vertices of SWITCH-gadget given `blocked` (vertex 0 forbidden) and `del` (vertex 6 forbidden)
private def swValid (blocked del : Bool) (v : Fin 7 → Bool) : Bool :=
  (!blocked || !(v 0)) && (!del || !(v 6)) &&
  !(v 0 && v 3) && !(v 0 && v 4) && !(v 1 && v 3) &&
  !(v 1 && v 5) && !(v 1 && v 6) && !(v 2 && v 4) && !(v 2 && v 5)

private lemma swAdj_six_nbr : ∀ b : Fin 7, swAdj 6 b = true → b.val = 1 := by decide

private lemma swValid_no_edge : ∀ (blk del : Bool) (s : Fin 7 → Bool) (ka kb : Fin 7),
    swValid blk del s = true → swAdj ka kb = true →
    s ka = true → s kb = true → False := by
  intro blk del s ka kb hs hab hka hkb
  dsimp only [swValid] at hs
  have hka' : ka = 0 ∨ ka = 1 ∨ ka = 2 ∨ ka = 3 ∨ ka = 4 ∨ ka = 5 ∨ ka = 6 := by
    rcases ka with ⟨k, hk⟩
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hkb' : kb = 0 ∨ kb = 1 ∨ kb = 2 ∨ kb = 3 ∨ kb = 4 ∨ kb = 5 ∨ kb = 6 := by
    rcases kb with ⟨k, hk⟩
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rcases hka' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hkb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [swAdj, hka, hkb] at hab hs

private def swCount (blocked del : Bool) : Nat :=
  ((Finset.univ : Finset (Fin 7 → Bool)).filter (fun v => swValid blocked del v = true)).card

private lemma swCount_mod2 :
    ∀ blocked del : Bool, swCount blocked del % 2 = if del = true ∧ blocked = false then 0 else 1 := by
  decide

/-! ### Part 2: Explicit graph on `N = 1 + 6 * n + 7 * m` vertices -/

private def totalN (n m : Nat) : Nat := 1 + 6 * n + 7 * m

private def hubV (n m : Nat) : Fin (totalN n m) := ⟨0, by dsimp [totalN]; omega⟩

private def notV (n m : Nat) (j : Fin n) (k : Fin 6) : Fin (totalN n m) :=
  ⟨1 + 6 * j.val + k.val, by dsimp [totalN]; have := j.isLt; have := k.isLt; omega⟩

private def swV (n m : Nat) (i : Fin m) (k : Fin 7) : Fin (totalN n m) :=
  ⟨1 + 6 * n + 7 * i.val + k.val, by dsimp [totalN]; have := i.isLt; have := k.isLt; omega⟩

private def pinV (n m : Nat) (j : Fin n) : Fin (totalN n m) := notV n m j ⟨0, by omega⟩
private def negV (n m : Nat) (j : Fin n) : Fin (totalN n m) := notV n m j ⟨1, by omega⟩
private def switchV (n m : Nat) (i : Fin m) : Fin (totalN n m) := swV n m i ⟨6, by omega⟩

private def litV (n m : Nat) (word : Fin m → Fin n → Bool) (i : Fin m) (j : Fin n) :
    Fin (totalN n m) :=
  if word i j then negV n m j else pinV n m j

private def shoreFn (n m : Nat) (v : Fin (totalN n m)) : Bool :=
  if v.val = 0 then false
  else if v.val < 1 + 6 * n then decide (3 ≤ (v.val - 1) % 6)
  else decide ((v.val - (1 + 6 * n)) % 7 < 3)

private lemma shoreFn_hub (n m : Nat) : shoreFn n m (hubV n m) = false := by
  simp [shoreFn, hubV]

private lemma shoreFn_notV (n m : Nat) (j : Fin n) (k : Fin 6) :
    shoreFn n m (notV n m j k) = c6Shore k := by
  dsimp only [shoreFn, notV, c6Shore]
  have hj := j.isLt; have hk := k.isLt
  have hne : 1 + 6 * j.val + k.val ≠ 0 := by omega
  have hlt : 1 + 6 * j.val + k.val < 1 + 6 * n := by omega
  have hmod : (1 + 6 * j.val + k.val - 1) % 6 = k.val := by
    have : 1 + 6 * j.val + k.val - 1 = k.val + 6 * j.val := by omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  rw [if_neg hne, if_pos hlt, hmod]

private lemma shoreFn_swV (n m : Nat) (i : Fin m) (k : Fin 7) :
    shoreFn n m (swV n m i k) = swShore k := by
  dsimp only [shoreFn, swV, swShore]
  have hk := k.isLt
  have hne : 1 + 6 * n + 7 * i.val + k.val ≠ 0 := by omega
  have hge : ¬ 1 + 6 * n + 7 * i.val + k.val < 1 + 6 * n := by omega
  have hmod : (1 + 6 * n + 7 * i.val + k.val - (1 + 6 * n)) % 7 = k.val := by
    have : 1 + 6 * n + 7 * i.val + k.val - (1 + 6 * n) = k.val + 7 * i.val := by omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  rw [if_neg hne, if_neg hge, hmod]

private lemma shoreFn_pinV (n m : Nat) (j : Fin n) : shoreFn n m (pinV n m j) = false := by
  dsimp only [pinV]; rw [shoreFn_notV]; decide

private lemma shoreFn_negV (n m : Nat) (j : Fin n) : shoreFn n m (negV n m j) = false := by
  dsimp only [negV]; rw [shoreFn_notV]; decide

private lemma shoreFn_litV (n m : Nat) (word : Fin m → Fin n → Bool) (i : Fin m) (j : Fin n) :
    shoreFn n m (litV n m word i j) = false := by
  dsimp only [litV]; split_ifs
  · exact shoreFn_negV n m j
  · exact shoreFn_pinV n m j

private def adjBool (n m : Nat) (word : Fin m → Fin n → Bool)
    (u v : Fin (totalN n m)) : Bool :=
  -- Internal C6 edges
  (if hu : 0 < u.val ∧ u.val < 1 + 6 * n then
    if hv : 0 < v.val ∧ v.val < 1 + 6 * n then
      decide ((u.val - 1) / 6 = (v.val - 1) / 6) &&
      c6Adj ⟨(u.val - 1) % 6, Nat.mod_lt _ (by omega)⟩
            ⟨(v.val - 1) % 6, Nat.mod_lt _ (by omega)⟩
    else false
   else false) ||
  -- Internal SWITCH edges
  (if hu : 1 + 6 * n ≤ u.val then
    if hv : 1 + 6 * n ≤ v.val then
      decide ((u.val - (1 + 6 * n)) / 7 = (v.val - (1 + 6 * n)) / 7) &&
      swAdj ⟨(u.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
            ⟨(v.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
    else false
   else false) ||
  -- Cross edges: swV i 0 <-> hub or litV i j
  (if hu : 1 + 6 * n ≤ u.val ∧ (u.val - (1 + 6 * n)) % 7 = 0 then
    let i : Fin m := ⟨(u.val - (1 + 6 * n)) / 7, by
      have := u.isLt; dsimp [totalN] at this; omega⟩
    decide (v = hubV n m) ||
    decide (∃ j : Fin n, v = litV n m word i j)
   else false) ||
  (if hv : 1 + 6 * n ≤ v.val ∧ (v.val - (1 + 6 * n)) % 7 = 0 then
    let i : Fin m := ⟨(v.val - (1 + 6 * n)) / 7, by
      have := v.isLt; dsimp [totalN] at this; omega⟩
    decide (u = hubV n m) ||
    decide (∃ j : Fin n, u = litV n m word i j)
   else false)

private def graphG (n m : Nat) (word : Fin m → Fin n → Bool)
    (u : Fin (totalN n m)) : Finset (Fin (totalN n m)) :=
  Finset.univ.filter (fun v => adjBool n m word u v = true)

private lemma adjBool_irrefl (n m : Nat) (word : Fin m → Fin n → Bool) (u : Fin (totalN n m)) :
    adjBool n m word u u = false := by
  dsimp only [adjBool]
  have h1 : (if hu : 0 < u.val ∧ u.val < 1 + 6 * n then
      if hv : 0 < u.val ∧ u.val < 1 + 6 * n then
        decide ((u.val - 1) / 6 = (u.val - 1) / 6) &&
        c6Adj ⟨(u.val - 1) % 6, Nat.mod_lt _ (by omega)⟩
              ⟨(u.val - 1) % 6, Nat.mod_lt _ (by omega)⟩
      else false else false) = false := by
    split_ifs <;> simp [c6Adj_irrefl]
  have h2 : (if hu : 1 + 6 * n ≤ u.val then
      if hv : 1 + 6 * n ≤ u.val then
        decide ((u.val - (1 + 6 * n)) / 7 = (u.val - (1 + 6 * n)) / 7) &&
        swAdj ⟨(u.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
              ⟨(u.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
      else false else false) = false := by
    split_ifs <;> simp [swAdj_irrefl]
  have h3 : (if hu : 1 + 6 * n ≤ u.val ∧ (u.val - (1 + 6 * n)) % 7 = 0 then
      let i : Fin m := ⟨(u.val - (1 + 6 * n)) / 7, by have := u.isLt; dsimp [totalN] at this; omega⟩
      decide (u = hubV n m) || decide (∃ j : Fin n, u = litV n m word i j)
      else false) = false := by
    split_ifs with hu
    · have hne_hub : u ≠ hubV n m := fun h => by
        have hv := congrArg Fin.val h; dsimp [hubV] at hv; omega
      have hne_lit : ¬ ∃ j : Fin n, u = litV n m word ⟨(u.val - (1 + 6 * n)) / 7, by
          have := u.isLt; dsimp [totalN] at this; omega⟩ j := by
        rintro ⟨j, hj⟩
        have hv := congrArg Fin.val hj
        dsimp only [litV, pinV, negV, notV] at hv
        split_ifs at hv <;> dsimp only at hv <;> (have := j.isLt; omega)
      simp [hne_hub, hne_lit]
    · rfl
  rw [h1, h2, h3]; rfl

private lemma adjBool_symm (n m : Nat) (word : Fin m → Fin n → Bool) (u v : Fin (totalN n m)) :
    adjBool n m word u v = adjBool n m word v u := by
  dsimp only [adjBool]
  have h1 : (if hu : 0 < u.val ∧ u.val < 1 + 6 * n then
      if hv : 0 < v.val ∧ v.val < 1 + 6 * n then
        decide ((u.val - 1) / 6 = (v.val - 1) / 6) &&
        c6Adj ⟨(u.val - 1) % 6, Nat.mod_lt _ (by omega)⟩
              ⟨(v.val - 1) % 6, Nat.mod_lt _ (by omega)⟩
      else false else false) =
      (if hv : 0 < v.val ∧ v.val < 1 + 6 * n then
      if hu : 0 < u.val ∧ u.val < 1 + 6 * n then
        decide ((v.val - 1) / 6 = (u.val - 1) / 6) &&
        c6Adj ⟨(v.val - 1) % 6, Nat.mod_lt _ (by omega)⟩
              ⟨(u.val - 1) % 6, Nat.mod_lt _ (by omega)⟩
      else false else false) := by
    by_cases hu : 0 < u.val ∧ u.val < 1 + 6 * n <;> by_cases hv : 0 < v.val ∧ v.val < 1 + 6 * n
    · rw [dite_eq_left hu, dite_eq_left hv, dite_eq_left hv, dite_eq_left hu, c6Adj_symm]
      congr 1; apply Bool.eq_iff_iff.mpr; simp [eq_comm]
    · simp [hu, hv]
    · simp [hu, hv]
    · simp [hu, hv]
  have h2 : (if hu : 1 + 6 * n ≤ u.val then
      if hv : 1 + 6 * n ≤ v.val then
        decide ((u.val - (1 + 6 * n)) / 7 = (v.val - (1 + 6 * n)) / 7) &&
        swAdj ⟨(u.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
              ⟨(v.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
      else false else false) =
      (if hv : 1 + 6 * n ≤ v.val then
      if hu : 1 + 6 * n ≤ u.val then
        decide ((v.val - (1 + 6 * n)) / 7 = (u.val - (1 + 6 * n)) / 7) &&
        swAdj ⟨(v.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
              ⟨(u.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
      else false else false) := by
    by_cases hu : 1 + 6 * n ≤ u.val <;> by_cases hv : 1 + 6 * n ≤ v.val
    · rw [dite_eq_left hu, dite_eq_left hv, dite_eq_left hv, dite_eq_left hu, swAdj_symm]
      congr 1; apply Bool.eq_iff_iff.mpr; simp [eq_comm]
    · simp [hu, hv]
    · simp [hu, hv]
    · simp [hu, hv]
  rw [h1, h2]
  generalize (if hv : 0 < v.val ∧ v.val < 1 + 6 * n then _ else false) = A
  generalize (if hv : 1 + 6 * n ≤ v.val then _ else false) = B
  generalize (if hu : 1 + 6 * n ≤ u.val ∧ (u.val - (1 + 6 * n)) % 7 = 0 then _ else false) = C
  generalize (if hv : 1 + 6 * n ≤ v.val ∧ (v.val - (1 + 6 * n)) % 7 = 0 then _ else false) = D
  cases A <;> cases B <;> cases C <;> cases D <;> rfl

private lemma adjBool_bip (n m : Nat) (word : Fin m → Fin n → Bool) (u v : Fin (totalN n m))
    (h : adjBool n m word u v = true) : shoreFn n m v ≠ shoreFn n m u := by
  dsimp only [adjBool] at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h1 | h2) | h3) | h4
  · split_ifs at h1 with hu hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    have hsu : shoreFn n m u = c6Shore ⟨(u.val - 1) % 6, Nat.mod_lt _ (by omega)⟩ := by
      dsimp only [shoreFn, c6Shore]; rw [ite_eq_right (by omega), ite_eq_left hu.2]
    have hsv : shoreFn n m v = c6Shore ⟨(v.val - 1) % 6, Nat.mod_lt _ (by omega)⟩ := by
      dsimp only [shoreFn, c6Shore]; rw [ite_eq_right (by omega), ite_eq_left hv.2]
    rw [hsu, hsv]; exact (c6Adj_bip _ _ h1.2).symm
  · split_ifs at h2 with hu hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    have hsu : shoreFn n m u = swShore ⟨(u.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩ := by
      dsimp only [shoreFn, swShore]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have hsv : shoreFn n m v = swShore ⟨(v.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩ := by
      dsimp only [shoreFn, swShore]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [hsu, hsv]; exact (swAdj_bip _ _ h2.2).symm
  · split_ifs at h3 with hu
    have hsu : shoreFn n m u = true := by
      dsimp only [shoreFn]; rw [ite_eq_right (by omega), ite_eq_right (by omega), hu.2]; decide
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h3
    have hsv : shoreFn n m v = false := by
      rcases h3 with rfl | ⟨j, rfl⟩
      · exact shoreFn_hub n m
      · exact shoreFn_litV n m word _ j
    rw [hsu, hsv]; decide
  · split_ifs at h4 with hv
    have hsv : shoreFn n m v = true := by
      dsimp only [shoreFn]; rw [ite_eq_right (by omega), ite_eq_right (by omega), hv.2]; decide
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h4
    have hsu : shoreFn n m u = false := by
      rcases h4 with rfl | ⟨j, rfl⟩
      · exact shoreFn_hub n m
      · exact shoreFn_litV n m word _ j
    rw [hsu, hsv]; decide

private lemma switch_deg_one (n m : Nat) (word : Fin m → Fin n → Bool) (i : Fin m) :
    (graphG n m word (switchV n m i)).card = 1 := by
  have heq : graphG n m word (switchV n m i) = {swV n m i ⟨1, by omega⟩} := by
    ext v
    simp only [graphG, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    have hsw_ge : 1 + 6 * n ≤ (switchV n m i).val := by dsimp [switchV, swV]; omega
    have hsw_div : ((switchV n m i).val - (1 + 6 * n)) / 7 = i.val := by
      dsimp [switchV, swV]; omega
    have hsw_mod : ((switchV n m i).val - (1 + 6 * n)) % 7 = 6 := by
      dsimp [switchV, swV]
      have : 1 + 6 * n + 7 * i.val + 6 - (1 + 6 * n) = 6 + 7 * i.val := by omega
      rw [this, Nat.add_mul_mod_self_left]
    have hsw_ne_hub : switchV n m i ≠ hubV n m := fun h => by
      have hv := congrArg Fin.val h; dsimp [switchV, swV, hubV] at hv; omega
    have hsw_ne_lit : ∀ i' j, switchV n m i ≠ litV n m word i' j := fun i' j h => by
      have hv := congrArg Fin.val h
      dsimp only [switchV, swV, litV, pinV, negV, notV] at hv
      split_ifs at hv <;> dsimp only at hv <;> (have := j.isLt; omega)
    constructor
    · intro hadj
      dsimp only [adjBool] at hadj
      have hnot1 : ¬ (0 < (switchV n m i).val ∧ (switchV n m i).val < 1 + 6 * n) := by omega
      have hnot3 : ¬ (1 + 6 * n ≤ (switchV n m i).val ∧ ((switchV n m i).val - (1 + 6 * n)) % 7 = 0) := by omega
      rw [dite_eq_right hnot1, dite_eq_right hnot3] at hadj
      have hb4 : (if hv : 1 + 6 * n ≤ v.val ∧ (v.val - (1 + 6 * n)) % 7 = 0 then
          let i' : Fin m := ⟨(v.val - (1 + 6 * n)) / 7, by have := v.isLt; dsimp [totalN] at this; omega⟩
          decide (switchV n m i = hubV n m) || decide (∃ j : Fin n, switchV n m i = litV n m word i' j)
          else false) = false := by
        split_ifs with hv
        · simp [hsw_ne_hub, hsw_ne_lit]
        · rfl
      rw [hb4] at hadj
      simp only [Bool.false_or, Bool.or_false] at hadj
      rw [dite_eq_left hsw_ge] at hadj
      split_ifs at hadj with hv_ge
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hadj
      rcases hadj with ⟨hdiv, hsw⟩
      have hmod6 : (⟨((switchV n m i).val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩ : Fin 7) = 6 :=
        Fin.ext hsw_mod
      rw [hmod6] at hsw
      have hv_mod : (v.val - (1 + 6 * n)) % 7 = 1 :=
        swAdj_six_nbr ⟨(v.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩ hsw
      apply Fin.ext
      dsimp only [swV]
      have hdiv_eq : (v.val - (1 + 6 * n)) / 7 = i.val := by omega
      omega
    · rintro rfl
      dsimp only [adjBool]
      have hge1 : 1 + 6 * n ≤ (swV n m i ⟨1, by omega⟩).val := by dsimp [swV]; omega
      have hdiv1 : ((swV n m i ⟨1, by omega⟩).val - (1 + 6 * n)) / 7 = i.val := by dsimp [swV]; omega
      have hmod1 : ((swV n m i ⟨1, by omega⟩).val - (1 + 6 * n)) % 7 = 1 := by
        dsimp [swV]
        have : 1 + 6 * n + 7 * i.val + 1 - (1 + 6 * n) = 1 + 7 * i.val := by omega
        rw [this, Nat.add_mul_mod_self_left]
      have h2 : (if hu : 1 + 6 * n ≤ (switchV n m i).val then
          if hv : 1 + 6 * n ≤ (swV n m i ⟨1, by omega⟩).val then
            decide (((switchV n m i).val - (1 + 6 * n)) / 7 = ((swV n m i ⟨1, by omega⟩).val - (1 + 6 * n)) / 7) &&
            swAdj ⟨((switchV n m i).val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
                  ⟨((swV n m i ⟨1, by omega⟩).val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
          else false else false) = true := by
        rw [dite_eq_left hsw_ge, dite_eq_left hge1, hsw_div, hdiv1]
        have hm6 : (⟨((switchV n m i).val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩ : Fin 7) =
            ⟨6, by omega⟩ := Fin.ext hsw_mod
        have hm1 : (⟨((swV n m i ⟨1, by omega⟩).val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩ : Fin 7) =
            ⟨1, by omega⟩ := Fin.ext hmod1
        rw [hm6, hm1]; simp [swAdj]
      rw [h2]; simp
  rw [heq, Finset.card_singleton]

/-! ### Part 3: Path decomposition of width `2 * n + 7` -/

private def coreBag (n m : Nat) : Finset (Fin (totalN n m)) :=
  {hubV n m} ∪ Finset.univ.image (pinV n m) ∪ Finset.univ.image (negV n m)

private lemma coreBag_card (n m : Nat) : (coreBag n m).card ≤ 2 * n + 1 := by
  dsimp only [coreBag]
  calc
    ({hubV n m} ∪ Finset.univ.image (pinV n m) ∪ Finset.univ.image (negV n m)).card
        ≤ ({hubV n m} ∪ Finset.univ.image (pinV n m)).card + (Finset.univ.image (negV n m)).card :=
          Finset.card_union_le _ _
    _ ≤ ({hubV n m} : Finset _).card + (Finset.univ.image (pinV n m)).card +
          (Finset.univ.image (negV n m)).card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 1 + (Finset.univ : Finset (Fin n)).card + (Finset.univ : Finset (Fin n)).card := by
          have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := pinV n m)
          have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin n))) (f := negV n m)
          simp only [Finset.card_singleton]; omega
    _ = 2 * n + 1 := by simp; omega

private def bagFn (n m : Nat) (t : Fin (1 + n + 2 * m)) : Finset (Fin (totalN n m)) :=
  if h0 : t.val = 0 then coreBag n m
  else if h1 : t.val < 1 + n then
    let j : Fin n := ⟨t.val - 1, by omega⟩
    coreBag n m ∪ Finset.univ.image (fun k : Fin 4 => notV n m j ⟨k.val + 2, by omega⟩)
  else
    let q := t.val - (1 + n)
    let i : Fin m := ⟨q / 2, by have := t.isLt; omega⟩
    if q % 2 = 0 then
      coreBag n m ∪ Finset.univ.image (fun k : Fin 6 => swV n m i ⟨k.val, by omega⟩)
    else
      coreBag n m ∪ {swV n m i ⟨1, by omega⟩, swV n m i ⟨6, by omega⟩}

private lemma bagFn_running_inter (n m : Nat) (v : Fin (totalN n m))
    (s t u : Fin (1 + n + 2 * m)) (hst : s ≤ t) (htu : t ≤ u)
    (hvs : v ∈ bagFn n m s) (hvu : v ∈ bagFn n m u) : v ∈ bagFn n m t := by
  by_cases hvc : v ∈ coreBag n m
  · dsimp only [bagFn]; split_ifs <;> first | exact hvc | exact Finset.mem_union_left _ hvc
  · let anchor : Nat :=
      if v.val < 1 + 6 * n then 1 + (v.val - 1) / 6
      else 1 + n + 2 * ((v.val - (1 + 6 * n)) / 7)
    have hloc : ∀ b : Fin (1 + n + 2 * m), v ∈ bagFn n m b →
        b.val = anchor ∨ b.val = anchor + 1 := by
      intro b hvb
      dsimp only [bagFn] at hvb
      split_ifs at hvb with hb0 hb1 hmod
      · exact absurd hvb hvc
      · rcases Finset.mem_union.mp hvb with hc | him
        · exact absurd hc hvc
        · rcases Finset.mem_image.mp him with ⟨k, _, rfl⟩
          left; dsimp only [anchor]
          rw [ite_eq_left (by dsimp only [notV]; omega)]
          dsimp only [notV]; omega
      · rcases Finset.mem_union.mp hvb with hc | him
        · exact absurd hc hvc
        · rcases Finset.mem_image.mp him with ⟨k, _, rfl⟩
          left; dsimp only [anchor]
          rw [ite_eq_right (by dsimp only [swV]; omega)]
          dsimp only [swV]; omega
      · rcases Finset.mem_union.mp hvb with hc | hp
        · exact absurd hc hvc
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl
          · right; dsimp only [anchor]
            rw [ite_eq_right (by dsimp only [swV]; omega)]
            dsimp only [swV]; omega
          · right; dsimp only [anchor]
            rw [ite_eq_right (by dsimp only [swV]; omega)]
            dsimp only [swV]; omega
    have hs := hloc s hvs
    have hu := hloc u hvu
    have hst' : s.val ≤ t.val := hst
    have htu' : t.val ≤ u.val := htu
    have hcases : t = s ∨ t = u := by
      rcases hs with hs' | hs' <;> rcases hu with hu' | hu'
      · left; exact Fin.ext (by omega)
      · by_cases hts : t.val = anchor
        · left; exact Fin.ext (by omega)
        · right; exact Fin.ext (by omega)
      · omega
      · left; exact Fin.ext (by omega)
    rcases hcases with rfl | rfl
    · exact hvs
    · exact hvu

private lemma exists_path_decomp (n m : Nat) (word : Fin m → Fin n → Bool) :
    ∃ (h : Nat) (bag : Fin h → Finset (Fin (totalN n m))),
      (∀ t, (bag t).card ≤ 2 * n + 7) ∧
      (∀ t j, pinV n m j ∈ bag t) ∧
      (∀ v, ∃ t, v ∈ bag t) ∧
      (∀ u v, v ∈ graphG n m word u → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
      ∀ v s t u, s ≤ t → t ≤ u → v ∈ bag s → v ∈ bag u → v ∈ bag t := by
  refine ⟨1 + n + 2 * m, bagFn n m, ?_, ?_, ?_, ?_, ?_⟩
  · -- card ≤ 2 * n + 7
    intro t
    have hc := coreBag_card n m
    dsimp only [bagFn]
    split_ifs
    · omega
    · have hle := Finset.card_union_le (coreBag n m)
        (Finset.univ.image (fun k : Fin 4 => notV n m ⟨t.val - 1, by omega⟩ ⟨k.val + 2, by omega⟩))
      have him := Finset.card_image_le (s := (Finset.univ : Finset (Fin 4)))
        (f := fun k : Fin 4 => notV n m ⟨t.val - 1, by omega⟩ ⟨k.val + 2, by omega⟩)
      simp only [Finset.card_univ, Fintype.card_fin] at him; omega
    · have hle := Finset.card_union_le (coreBag n m)
        (Finset.univ.image (fun k : Fin 6 => swV n m ⟨(t.val - (1 + n)) / 2, by have := t.isLt; omega⟩ ⟨k.val, by omega⟩))
      have him := Finset.card_image_le (s := (Finset.univ : Finset (Fin 6)))
        (f := fun k : Fin 6 => swV n m ⟨(t.val - (1 + n)) / 2, by have := t.isLt; omega⟩ ⟨k.val, by omega⟩)
      simp only [Finset.card_univ, Fintype.card_fin] at him; omega
    · have hle := Finset.card_union_le (coreBag n m)
        ({swV n m ⟨(t.val - (1 + n)) / 2, by have := t.isLt; omega⟩ ⟨1, by omega⟩,
          swV n m ⟨(t.val - (1 + n)) / 2, by have := t.isLt; omega⟩ ⟨6, by omega⟩} : Finset _)
      have hpair : ({swV n m ⟨(t.val - (1 + n)) / 2, by have := t.isLt; omega⟩ ⟨1, by omega⟩,
          swV n m ⟨(t.val - (1 + n)) / 2, by have := t.isLt; omega⟩ ⟨6, by omega⟩} : Finset _).card ≤ 2 :=
        Finset.card_le_two
      omega
  · -- pinV j ∈ bag t
    intro t j
    have hp : pinV n m j ∈ coreBag n m :=
      Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
    dsimp only [bagFn]; split_ifs <;> first | exact hp | exact Finset.mem_union_left _ hp
  · -- ∀ v, ∃ t, v ∈ bag t
    intro v
    by_cases hv0 : v.val = 0
    · refine ⟨⟨0, by omega⟩, ?_⟩
      have heq : v = hubV n m := Fin.ext hv0
      rw [heq]; dsimp only [bagFn]; rw [dite_eq_left rfl]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
    · by_cases hv1 : v.val < 1 + 6 * n
      · let j : Fin n := ⟨(v.val - 1) / 6, by omega⟩
        let r := (v.val - 1) % 6
        have hv_eq : v = notV n m j ⟨r, Nat.mod_lt _ (by omega)⟩ := Fin.ext (by dsimp [notV, j, r]; omega)
        by_cases hr2 : r < 2
        · refine ⟨⟨0, by omega⟩, ?_⟩
          suffices h : notV n m j ⟨r, Nat.mod_lt _ (by omega)⟩ ∈ bagFn n m ⟨0, by omega⟩ by
            rwa [← hv_eq] at h
          dsimp only [bagFn]; rw [dite_eq_left rfl]
          have hr01 : r = 0 ∨ r = 1 := by omega
          rcases hr01 with h0 | h1
          · have : notV n m j ⟨r, Nat.mod_lt _ (by omega)⟩ = pinV n m j := Fin.ext (by dsimp [notV, pinV]; omega)
            rw [this]
            exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
          · have : notV n m j ⟨r, Nat.mod_lt _ (by omega)⟩ = negV n m j := Fin.ext (by dsimp [notV, negV]; omega)
            rw [this]
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
        · refine ⟨⟨1 + j.val, by have := j.isLt; omega⟩, ?_⟩
          suffices h : notV n m j ⟨r, Nat.mod_lt _ (by omega)⟩ ∈ bagFn n m ⟨1 + j.val, by have := j.isLt; omega⟩ by
            rwa [← hv_eq] at h
          dsimp only [bagFn]
          rw [dite_eq_right (by omega), dite_eq_left (by have := j.isLt; omega)]
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨r - 2, by omega⟩, Finset.mem_univ _, ?_⟩)
          exact Fin.ext (by dsimp [notV, j]; omega)
      · let i : Fin m := ⟨(v.val - (1 + 6 * n)) / 7, by have := v.isLt; dsimp [totalN] at this; omega⟩
        let r := (v.val - (1 + 6 * n)) % 7
        have hv_eq : v = swV n m i ⟨r, Nat.mod_lt _ (by omega)⟩ := Fin.ext (by dsimp [swV, i, r]; omega)
        by_cases hr6 : r < 6
        · refine ⟨⟨1 + n + 2 * i.val, by have := i.isLt; omega⟩, ?_⟩
          suffices h : swV n m i ⟨r, Nat.mod_lt _ (by omega)⟩ ∈ bagFn n m ⟨1 + n + 2 * i.val, by have := i.isLt; omega⟩ by
            rwa [← hv_eq] at h
          dsimp only [bagFn]
          rw [dite_eq_right (by omega), dite_eq_right (by omega)]
          have hmod : (1 + n + 2 * i.val - (1 + n)) % 2 = 0 := by omega
          rw [ite_eq_left hmod]
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨r, hr6⟩, Finset.mem_univ _, ?_⟩)
          exact Fin.ext (by dsimp [swV, i]; omega)
        · refine ⟨⟨1 + n + 2 * i.val + 1, by have := i.isLt; omega⟩, ?_⟩
          suffices h : swV n m i ⟨r, Nat.mod_lt _ (by omega)⟩ ∈ bagFn n m ⟨1 + n + 2 * i.val + 1, by have := i.isLt; omega⟩ by
            rwa [← hv_eq] at h
          dsimp only [bagFn]
          rw [dite_eq_right (by omega), dite_eq_right (by omega)]
          have hmod : ¬ (1 + n + 2 * i.val + 1 - (1 + n)) % 2 = 0 := by omega
          rw [ite_eq_right hmod]
          refine Finset.mem_union_right _ ?_
          have hreq : r = 6 := by omega
          have hveq : swV n m i ⟨r, Nat.mod_lt _ (by omega)⟩ =
              swV n m ⟨(1 + n + 2 * i.val + 1 - (1 + n)) / 2, by have := i.isLt; omega⟩ ⟨6, by omega⟩ :=
            Fin.ext (by dsimp [swV, i]; omega)
          rw [hveq]; simp
  · -- Edge coverage
    intro u v huv
    simp only [graphG, Finset.mem_filter, Finset.mem_univ, true_and] at huv
    have hcore_in : ∀ t (w : Fin (totalN n m)), w ∈ coreBag n m → w ∈ bagFn n m t := by
      intro t w hw; dsimp only [bagFn]; split_ifs <;> first | exact hw | exact Finset.mem_union_left _ hw
    have hhub_core : hubV n m ∈ coreBag n m :=
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
    have hlit_core : ∀ i j, litV n m word i j ∈ coreBag n m := by
      intro i j; dsimp only [litV]; split_ifs
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
    dsimp only [adjBool] at huv
    simp only [Bool.or_eq_true] at huv
    rcases huv with ((h1 | h2) | h3) | h4
    · -- Internal C6 edge -> bag 1 + j
      split_ifs at h1 with hu hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      let j : Fin n := ⟨(u.val - 1) / 6, by omega⟩
      have hmem_not : ∀ w : Fin (totalN n m), 0 < w.val ∧ w.val < 1 + 6 * n →
            (w.val - 1) / 6 = j.val → w ∈ bagFn n m ⟨1 + j.val, by have := j.isLt; omega⟩ := by
        intro w hw hdiv
        have hjd : (w.val - 1) / 6 = (u.val - 1) / 6 := hdiv
        by_cases hmod : (w.val - 1) % 6 < 2
        · refine hcore_in _ w ?_
          have h01 : (w.val - 1) % 6 = 0 ∨ (w.val - 1) % 6 = 1 := by omega
          rcases h01 with hm | hm
          · have : w = pinV n m j := Fin.ext (by dsimp only [pinV, notV, j]; omega)
            rw [this]; exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
          · have : w = negV n m j := Fin.ext (by dsimp only [negV, notV, j]; omega)
            rw [this]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
        · dsimp only [bagFn]
          rw [dite_eq_right (by omega), dite_eq_left (by have := j.isLt; omega)]
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨(w.val - 1) % 6 - 2, by omega⟩, Finset.mem_univ _, ?_⟩)
          exact Fin.ext (by dsimp only [notV, j]; omega)
      exact ⟨⟨1 + j.val, by have := j.isLt; omega⟩, hmem_not u hu rfl, hmem_not v hv h1.1.symm⟩
    · -- Internal SWITCH edge -> either 1 + n + 2*i (both < 6) or 1 + n + 2*i + 1 ({1, 6})
      split_ifs at h2 with hu hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      let i : Fin m := ⟨(u.val - (1 + 6 * n)) / 7, by have := u.isLt; dsimp [totalN] at this; omega⟩
      set ru := (u.val - (1 + 6 * n)) % 7
      set rv := (v.val - (1 + 6 * n)) % 7
      by_cases h6 : ru = 6 ∨ rv = 6
      · have hpair := swAdj_six ⟨ru, Nat.mod_lt _ (by omega)⟩ ⟨rv, Nat.mod_lt _ (by omega)⟩ h2.2 h6
        have hdiv_i : (1 + n + 2 * i.val + 1 - (1 + n)) / 2 = i.val := by omega
        have hu_eq : u.val = 1 + 6 * n + 7 * i.val + ru := by
          have : i.val = (u.val - (1 + 6 * n)) / 7 := rfl
          have : ru = (u.val - (1 + 6 * n)) % 7 := rfl
          omega
        have hv_eq : v.val = 1 + 6 * n + 7 * i.val + rv := by
          have : i.val = (v.val - (1 + 6 * n)) / 7 := h2.1
          have : rv = (v.val - (1 + 6 * n)) % 7 := rfl
          omega
        refine ⟨⟨1 + n + 2 * i.val + 1, by have := i.isLt; omega⟩, ?_, ?_⟩
        · dsimp only [bagFn]
          rw [dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega)]
          refine Finset.mem_union_right _ ?_
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hpair.1 with h1 | h6'
          · left; apply Fin.ext
            change u.val = 1 + 6 * n + 7 * ((1 + n + 2 * i.val + 1 - (1 + n)) / 2) + 1
            rw [hdiv_i]; have hru : ru = 1 := h1; omega
          · right; apply Fin.ext
            change u.val = 1 + 6 * n + 7 * ((1 + n + 2 * i.val + 1 - (1 + n)) / 2) + 6
            rw [hdiv_i]; have hru : ru = 6 := h6'; omega
        · dsimp only [bagFn]
          rw [dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_right (by omega)]
          refine Finset.mem_union_right _ ?_
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hpair.2 with h1 | h6'
          · left; apply Fin.ext
            change v.val = 1 + 6 * n + 7 * ((1 + n + 2 * i.val + 1 - (1 + n)) / 2) + 1
            rw [hdiv_i]; have hrv : rv = 1 := h1; omega
          · right; apply Fin.ext
            change v.val = 1 + 6 * n + 7 * ((1 + n + 2 * i.val + 1 - (1 + n)) / 2) + 6
            rw [hdiv_i]; have hrv : rv = 6 := h6'; omega
      · have hru6 : ru < 6 := by have : ru < 7 := Nat.mod_lt _ (by omega); omega
        have hrv6 : rv < 6 := by have : rv < 7 := Nat.mod_lt _ (by omega); omega
        refine ⟨⟨1 + n + 2 * i.val, by have := i.isLt; omega⟩, ?_, ?_⟩
        · dsimp only [bagFn]
          rw [dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_left (by omega)]
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨ru, hru6⟩, Finset.mem_univ _, ?_⟩)
          exact Fin.ext (by dsimp only [swV, i]; omega)
        · dsimp only [bagFn]
          rw [dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_left (by omega)]
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨rv, hrv6⟩, Finset.mem_univ _, ?_⟩)
          exact Fin.ext (by dsimp only [swV, i]; omega)
    · -- Cross edge: u = swV i 0, v ∈ coreBag -> bag 1 + n + 2*i
      split_ifs at h3 with hu
      let i : Fin m := ⟨(u.val - (1 + 6 * n)) / 7, by have := u.isLt; dsimp [totalN] at this; omega⟩
      refine ⟨⟨1 + n + 2 * i.val, by have := i.isLt; omega⟩, ?_, ?_⟩
      · dsimp only [bagFn]
        rw [dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_left (by omega)]
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩)
        exact Fin.ext (by dsimp only [swV, i]; omega)
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at h3
        rcases h3 with rfl | ⟨j, rfl⟩
        · exact hcore_in _ _ hhub_core
        · exact hcore_in _ _ (hlit_core i j)
    · -- Cross edge: v = swV i 0, u ∈ coreBag -> bag 1 + n + 2*i
      split_ifs at h4 with hv
      let i : Fin m := ⟨(v.val - (1 + 6 * n)) / 7, by have := v.isLt; dsimp [totalN] at this; omega⟩
      refine ⟨⟨1 + n + 2 * i.val, by have := i.isLt; omega⟩, ?_, ?_⟩
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at h4
        rcases h4 with rfl | ⟨j, rfl⟩
        · exact hcore_in _ _ hhub_core
        · exact hcore_in _ _ (hlit_core i j)
      · dsimp only [bagFn]
        rw [dite_eq_right (by omega), dite_eq_right (by omega), ite_eq_left (by omega)]
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩)
        exact Fin.ext (by dsimp only [swV, i]; omega)
  · exact bagFn_running_inter n m

/-! ### Part 4: Exact IS factorization and mod-2 count -/

private def isValidIS (n m : Nat) (word : Fin m → Fin n → Bool)
    (f : Fin m → Bool) (x : Fin n → Bool) (I : Finset (Fin (totalN n m))) : Prop :=
  (∀ v ∈ I, ∀ i : Fin m, v = switchV n m i → f i = false) ∧
  (∀ j : Fin n, pinV n m j ∈ I ↔ x j = true) ∧
  (∀ u ∈ I, ∀ v ∈ graphG n m word u, v ∉ I)

private noncomputable def validISSet (n m : Nat) (word : Fin m → Fin n → Bool)
    (f : Fin m → Bool) (x : Fin n → Bool) : Finset (Finset (Fin (totalN n m))) := by
  classical
  exact Finset.univ.filter (fun I => isValidIS n m word f x I)

private lemma mem_validISSet (n m : Nat) (word : Fin m → Fin n → Bool)
    (f : Fin m → Bool) (x : Fin n → Bool) (I : Finset (Fin (totalN n m))) :
    I ∈ validISSet n m word f x ↔ isValidIS n m word f x I := by
  classical simp [validISSet]

private noncomputable def fiberISSet (n m : Nat) (word : Fin m → Fin n → Bool)
    (f : Fin m → Bool) (x : Fin n → Bool) (hBit : Bool) (negB : Fin n → Bool) :
    Finset (Finset (Fin (totalN n m))) := by
  classical
  exact Finset.univ.filter (fun I =>
    isValidIS n m word f x I ∧
    decide (hubV n m ∈ I) = hBit ∧
    (fun j : Fin n => decide (negV n m j ∈ I)) = negB)

private lemma mem_fiberISSet (n m : Nat) (word : Fin m → Fin n → Bool)
    (f : Fin m → Bool) (x : Fin n → Bool) (hBit : Bool) (negB : Fin n → Bool)
    (I : Finset (Fin (totalN n m))) :
    I ∈ fiberISSet n m word f x hBit negB ↔
      isValidIS n m word f x I ∧
      decide (hubV n m ∈ I) = hBit ∧
      (fun j : Fin n => decide (negV n m j ∈ I)) = negB := by
  classical simp [fiberISSet]

private def blockedBit (n m : Nat) (word : Fin m → Fin n → Bool)
    (hBit : Bool) (x negB : Fin n → Bool) (i : Fin m) : Bool :=
  hBit || decide (∃ j : Fin n, (if word i j then negB j else x j) = true)

private lemma fiber_card_is (n m : Nat) (word : Fin m → Fin n → Bool)
    (f : Fin m → Bool) (x : Fin n → Bool) (hBit : Bool) (negB : Fin n → Bool) :
    (fiberISSet n m word f x hBit negB).card =
    (∏ j : Fin n, notCount (x j) (negB j)) *
    (∏ i : Fin m, swCount (blockedBit n m word hBit x negB i) (f i)) := by
  classical
  let NotSet (j : Fin n) : Finset (Fin 4 → Bool) :=
    Finset.univ.filter (fun c => notValid (x j) (negB j) c = true)
  let SwSet (i : Fin m) : Finset (Fin 7 → Bool) :=
    Finset.univ.filter (fun v => swValid (blockedBit n m word hBit x negB i) (f i) v = true)
  let ProdSet := (Fintype.piFinset NotSet) ×ˢ (Fintype.piFinset SwSet)
  have hProdCard : ProdSet.card =
      (∏ j : Fin n, notCount (x j) (negB j)) *
      (∏ i : Fin m, swCount (blockedBit n m word hBit x negB i) (f i)) := by
    rw [Finset.card_product, Fintype.card_piFinset, Fintype.card_piFinset]
    rfl
  rw [← hProdCard]
  -- Map each I to (c, s)
  let toPair : Finset (Fin (totalN n m)) →
      (Fin n → Fin 4 → Bool) × (Fin m → Fin 7 → Bool) := fun I =>
    (fun j k => decide (notV n m j ⟨k.val + 2, by omega⟩ ∈ I),
     fun i k => decide (swV n m i k ∈ I))
  let ofPair : (Fin n → Fin 4 → Bool) × (Fin m → Fin 7 → Bool) →
      Finset (Fin (totalN n m)) := fun p =>
    Finset.univ.filter (fun v =>
      if h0 : v.val = 0 then hBit = true
      else if h1 : v.val < 1 + 6 * n then
        let j : Fin n := ⟨(v.val - 1) / 6, by omega⟩
        let r := (v.val - 1) % 6
        if r = 0 then x j = true
        else if r = 1 then negB j = true
        else p.1 j ⟨r - 2, by omega⟩ = true
      else
        let i : Fin m := ⟨(v.val - (1 + 6 * n)) / 7, by have := v.isLt; dsimp [totalN] at this; omega⟩
        let r : Fin 7 := ⟨(v.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
        p.2 i r = true)
  have hadj_not : ∀ (j : Fin n) (a b : Fin 6),
      c6Adj a b = true → notV n m j b ∈ graphG n m word (notV n m j a) := by
    intro j a b hab
    simp only [graphG, Finset.mem_filter, Finset.mem_univ, true_and, adjBool]
    have ha := a.isLt; have hb := b.isLt; have hj := j.isLt
    have h1 : (if hu : 0 < (notV n m j a).val ∧ (notV n m j a).val < 1 + 6 * n then
        if hv : 0 < (notV n m j b).val ∧ (notV n m j b).val < 1 + 6 * n then
          decide (((notV n m j a).val - 1) / 6 = ((notV n m j b).val - 1) / 6) &&
          c6Adj ⟨((notV n m j a).val - 1) % 6, Nat.mod_lt _ (by omega)⟩
                ⟨((notV n m j b).val - 1) % 6, Nat.mod_lt _ (by omega)⟩
        else false else false) = true := by
      have hua : 0 < (notV n m j a).val ∧ (notV n m j a).val < 1 + 6 * n := by dsimp [notV]; omega
      have hvb : 0 < (notV n m j b).val ∧ (notV n m j b).val < 1 + 6 * n := by dsimp [notV]; omega
      rw [dite_eq_left hua, dite_eq_left hvb]
      have hda : ((notV n m j a).val - 1) / 6 = j.val := by dsimp [notV]; omega
      have hdb : ((notV n m j b).val - 1) / 6 = j.val := by dsimp [notV]; omega
      have hma : (⟨((notV n m j a).val - 1) % 6, Nat.mod_lt _ (by omega)⟩ : Fin 6) = a := by
        apply Fin.ext; dsimp [notV]
        have : 1 + 6 * j.val + a.val - 1 = a.val + 6 * j.val := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      have hmb : (⟨((notV n m j b).val - 1) % 6, Nat.mod_lt _ (by omega)⟩ : Fin 6) = b := by
        apply Fin.ext; dsimp [notV]
        have : 1 + 6 * j.val + b.val - 1 = b.val + 6 * j.val := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
      rw [hda, hdb, hma, hmb, hab]; simp
    rw [h1]; simp
  have hadj_sw : ∀ (i : Fin m) (a b : Fin 7),
      swAdj a b = true → swV n m i b ∈ graphG n m word (swV n m i a) := by
    intro i a b hab
    simp only [graphG, Finset.mem_filter, Finset.mem_univ, true_and, adjBool]
    have ha := a.isLt; have hb := b.isLt
    have h2 : (if hu : 1 + 6 * n ≤ (swV n m i a).val then
        if hv : 1 + 6 * n ≤ (swV n m i b).val then
          decide (((swV n m i a).val - (1 + 6 * n)) / 7 = ((swV n m i b).val - (1 + 6 * n)) / 7) &&
          swAdj ⟨((swV n m i a).val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
                ⟨((swV n m i b).val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
        else false else false) = true := by
      have hua : 1 + 6 * n ≤ (swV n m i a).val := by dsimp [swV]; omega
      have hvb : 1 + 6 * n ≤ (swV n m i b).val := by dsimp [swV]; omega
      rw [dite_eq_left hua, dite_eq_left hvb]
      have hda : ((swV n m i a).val - (1 + 6 * n)) / 7 = i.val := by dsimp [swV]; omega
      have hdb : ((swV n m i b).val - (1 + 6 * n)) / 7 = i.val := by dsimp [swV]; omega
      have hma : (⟨((swV n m i a).val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩ : Fin 7) = a := by
        apply Fin.ext; dsimp [swV]
        have : 1 + 6 * n + 7 * i.val + a.val - (1 + 6 * n) = a.val + 7 * i.val := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      have hmb : (⟨((swV n m i b).val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩ : Fin 7) = b := by
        apply Fin.ext; dsimp [swV]
        have : 1 + 6 * n + 7 * i.val + b.val - (1 + 6 * n) = b.val + 7 * i.val := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
      rw [hda, hdb, hma, hmb, hab]; simp
    rw [h2]; simp
  have hadj_cross_hub : ∀ i : Fin m, hubV n m ∈ graphG n m word (swV n m i 0) := by
    intro i
    simp only [graphG, Finset.mem_filter, Finset.mem_univ, true_and, adjBool]
    have hcond : 1 + 6 * n ≤ (swV n m i 0).val ∧ ((swV n m i 0).val - (1 + 6 * n)) % 7 = 0 := by
      dsimp [swV]; constructor
      · omega
      · have : 1 + 6 * n + 7 * i.val - (1 + 6 * n) = 7 * i.val := by omega
        rw [this, Nat.mul_mod_right]
    rw [dite_eq_left hcond]; simp
  have hadj_cross_lit : ∀ (i : Fin m) (j : Fin n),
      litV n m word i j ∈ graphG n m word (swV n m i 0) := by
    intro i j
    simp only [graphG, Finset.mem_filter, Finset.mem_univ, true_and, adjBool]
    have hcond : 1 + 6 * n ≤ (swV n m i 0).val ∧ ((swV n m i 0).val - (1 + 6 * n)) % 7 = 0 := by
      dsimp [swV]; constructor
      · omega
      · have : 1 + 6 * n + 7 * i.val - (1 + 6 * n) = 7 * i.val := by omega
        rw [this, Nat.mul_mod_right]
    rw [dite_eq_left hcond]
    have hi' : (⟨((swV n m i 0).val - (1 + 6 * n)) / 7,
        by have := (swV n m i 0).isLt; dsimp [totalN] at this; omega⟩ : Fin m) = i :=
      Fin.ext (by dsimp [swV]; omega)
    simp only [hi', Bool.or_eq_true, decide_eq_true_eq]
    left; right; right; exact ⟨j, rfl⟩
  refine Finset.card_bij (fun I _ => toPair I) ?_ ?_ ?_
  · -- Maps into ProdSet
    intro I hI
    rw [mem_fiberISSet] at hI
    simp only [isValidIS] at hI
    rcases hI with ⟨⟨hlive, hpin, hind⟩, hhub, hneg⟩
    simp only [ProdSet, Finset.mem_product, Fintype.mem_piFinset, NotSet, SwSet,
      Finset.mem_filter, Finset.mem_univ, true_and]
    have hneg_j : ∀ j : Fin n, negV n m j ∈ I ↔ negB j = true := by
      intro j
      have h := congrFun hneg j
      rw [← h]; simp
    have hhub_iff : hubV n m ∈ I ↔ hBit = true := by
      rw [← hhub]; simp
    constructor
    · intro j
      dsimp only [notValid, toPair]
      have hno : ∀ a b : Fin 6, c6Adj a b = true →
          !(decide (notV n m j a ∈ I) && decide (notV n m j b ∈ I)) = true := by
        intro a b hab
        by_cases ha : notV n m j a ∈ I
        · have hb : notV n m j b ∉ I := hind _ ha _ (hadj_not j a b hab)
          simp [ha, hb]
        · simp [ha]
      have h0 : x j = decide (notV n m j 0 ∈ I) := by
        apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq]; exact (hpin j).symm
      have h1 : negB j = decide (notV n m j 1 ∈ I) := by
        apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq]; exact (hneg_j j).symm
      rw [h0, h1]
      simp only [Bool.and_eq_true]
      refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact hno 0 3 rfl
      · exact hno 0 4 rfl
      · exact hno 1 3 rfl
      · exact hno 1 5 rfl
      · exact hno 2 4 rfl
      · exact hno 2 5 rfl
    · intro i
      dsimp only [swValid, toPair]
      have hno : ∀ a b : Fin 7, swAdj a b = true →
          !(decide (swV n m i a ∈ I) && decide (swV n m i b ∈ I)) = true := by
        intro a b hab
        by_cases ha : swV n m i a ∈ I
        · have hb : swV n m i b ∉ I := hind _ ha _ (hadj_sw i a b hab)
          simp [ha, hb]
        · simp [ha]
      have hblk : (!blockedBit n m word hBit x negB i || !(decide (swV n m i 0 ∈ I))) = true := by
        by_cases h0 : swV n m i 0 ∈ I
        · have hbf : blockedBit n m word hBit x negB i = false := by
            dsimp only [blockedBit]
            have hhf : hBit = false := by
              by_contra hht
              have hht' : hBit = true := by cases hBit <;> simp_all
              exact hind _ h0 _ (hadj_cross_hub i) (hhub_iff.mpr hht')
            have hno_lit : ¬ ∃ j : Fin n, (if word i j then negB j else x j) = true := by
              rintro ⟨j, hj⟩
              have hlit_in : litV n m word i j ∈ I := by
                dsimp only [litV]
                cases hw : word i j
                · rw [hw] at hj; simp only [Bool.false_eq_true, ↓reduceIte] at hj ⊢
                  exact (hpin j).mpr hj
                · rw [hw] at hj; simp only [↓reduceIte] at hj ⊢
                  exact (hneg_j j).mpr hj
              exact hind _ h0 _ (hadj_cross_lit i j) hlit_in
            rw [hhf, Bool.false_or, decide_eq_false hno_lit]
          simp [hbf]
        · simp [h0]
      have hdel : (!(f i) || !(decide (swV n m i 6 ∈ I))) = true := by
        by_cases h6 : swV n m i 6 ∈ I
        · have hf0 : f i = false := hlive _ h6 i rfl
          simp [hf0]
        · simp [h6]
      simp only [Bool.and_eq_true]
      refine ⟨⟨⟨⟨⟨⟨⟨⟨hblk, hdel⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact hno 0 3 rfl
      · exact hno 0 4 rfl
      · exact hno 1 3 rfl
      · exact hno 1 5 rfl
      · exact hno 1 6 rfl
      · exact hno 2 4 rfl
      · exact hno 2 5 rfl
  · -- Injective
    intro I1 hI1 I2 hI2 heq
    rw [mem_fiberISSet] at hI1 hI2
    simp only [isValidIS] at hI1 hI2
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    ext v
    by_cases hv0 : v.val = 0
    · have : v = hubV n m := Fin.ext hv0
      rw [this]; rw [← hI1.2.1] at hI2
      have hb : decide (hubV n m ∈ I1) = decide (hubV n m ∈ I2) := hI2.2.1.symm
      simpa using congrArg (· = true) hb
    · by_cases hv1 : v.val < 1 + 6 * n
      · let j : Fin n := ⟨(v.val - 1) / 6, by omega⟩
        let r := (v.val - 1) % 6
        by_cases hr0 : r = 0
        · have : v = pinV n m j := Fin.ext (by dsimp [pinV, notV, j]; omega)
          rw [this, hI1.1.2.1 j, hI2.1.2.1 j]
        · by_cases hr1 : r = 1
          · have : v = negV n m j := Fin.ext (by dsimp [negV, notV, j]; omega)
            rw [this]
            have hnj := congrFun (hI1.2.2.trans hI2.2.2.symm) j
            simpa using congrArg (· = true) hnj
          · have : v = notV n m j ⟨(r - 2) + 2, by omega⟩ := Fin.ext (by dsimp [notV, j]; omega)
            rw [this]
            have hjk := congrFun (congrFun h1 j) ⟨r - 2, by omega⟩
            dsimp only [toPair] at hjk
            simpa using congrArg (· = true) hjk
      · let i : Fin m := ⟨(v.val - (1 + 6 * n)) / 7, by have := v.isLt; dsimp [totalN] at this; omega⟩
        let r : Fin 7 := ⟨(v.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
        have : v = swV n m i r := Fin.ext (by dsimp [swV, i, r]; omega)
        rw [this]
        have hir := congrFun (congrFun h2 i) r
        dsimp only [toPair] at hir
        simpa using congrArg (· = true) hir
  · -- Surjective: ofPair p is a valid IS in the fiber with toPair (ofPair p) = p
    rintro ⟨c, s⟩ hp
    simp only [ProdSet, Finset.mem_product, Fintype.mem_piFinset, NotSet, SwSet,
      Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨hc, hs⟩
    let I := ofPair (c, s)
    have hmem_hub : hubV n m ∈ I ↔ hBit = true := by
      simp [I, ofPair, hubV]
    have hmem_not : ∀ (j : Fin n) (k : Fin 6),
        notV n m j k ∈ I ↔ notBit (x j) (negB j) (c j) k = true := by
      intro j k
      have hj := j.isLt; have hk := k.isLt
      simp only [I, ofPair, Finset.mem_filter, Finset.mem_univ, true_and, notBit]
      have hne0 : (notV n m j k).val ≠ 0 := by dsimp [notV]; omega
      have hlt1 : (notV n m j k).val < 1 + 6 * n := by dsimp [notV]; omega
      rw [dite_eq_right hne0, dite_eq_left hlt1]
      have hdiv : ((notV n m j k).val - 1) / 6 = j.val := by dsimp [notV]; omega
      have hmod : ((notV n m j k).val - 1) % 6 = k.val := by
        dsimp [notV]
        have : 1 + 6 * j.val + k.val - 1 = k.val + 6 * j.val := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
      have hj_eq : (⟨((notV n m j k).val - 1) / 6, by omega⟩ : Fin n) = j := Fin.ext hdiv
      simp only [hj_eq, hmod]
      fin_cases k <;> simp
    have hmem_sw : ∀ (i : Fin m) (k : Fin 7), swV n m i k ∈ I ↔ s i k = true := by
      intro i k
      have hk := k.isLt
      simp only [I, ofPair, Finset.mem_filter, Finset.mem_univ, true_and]
      have hne0 : (swV n m i k).val ≠ 0 := by dsimp [swV]; omega
      have hge1 : ¬ (swV n m i k).val < 1 + 6 * n := by dsimp [swV]; omega
      rw [dite_eq_right hne0, dite_eq_right hge1]
      have hi_eq : (⟨((swV n m i k).val - (1 + 6 * n)) / 7,
          by have := (swV n m i k).isLt; dsimp [totalN] at this; omega⟩ : Fin m) = i :=
        Fin.ext (by dsimp [swV]; omega)
      have hk_eq : (⟨((swV n m i k).val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩ : Fin 7) = k := by
        apply Fin.ext; dsimp [swV]
        have : 1 + 6 * n + 7 * i.val + k.val - (1 + 6 * n) = k.val + 7 * i.val := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
      rw [hi_eq, hk_eq]
    refine ⟨I, ?_, ?_⟩
    · rw [mem_fiberISSet]
      simp only [isValidIS]
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · intro v hv i rfl
        have hs6 : s i 6 = true := (hmem_sw i 6).mp hv
        have hsi := hs i
        dsimp only [swValid] at hsi
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hsi
        have hdel := hsi.1.1.1.1.1.1.1.2
        rcases hdel with hf | h6f
        · exact hf
        · rw [hs6] at h6f; cases h6f
      · intro j; exact hmem_not j 0
      · -- Independence of I
        intro u hu v huv hvI
        simp only [graphG, Finset.mem_filter, Finset.mem_univ, true_and, adjBool, Bool.or_eq_true] at huv
        rcases huv with ((h1 | h2) | h3) | h4
        · -- C6 internal edge
          split_ifs at h1 with hu1 hv1
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
          let j : Fin n := ⟨(u.val - 1) / 6, by omega⟩
          let ka : Fin 6 := ⟨(u.val - 1) % 6, Nat.mod_lt _ (by omega)⟩
          let kb : Fin 6 := ⟨(v.val - 1) % 6, Nat.mod_lt _ (by omega)⟩
          have hueq : u = notV n m j ka := Fin.ext (by dsimp [notV, j, ka]; omega)
          have hveq : v = notV n m j kb := Fin.ext (by dsimp [notV, j, kb]; omega)
          rw [hueq] at hu; rw [hveq] at hvI
          exact notValid_no_edge (x j) (negB j) (c j) ka kb (hc j) h1.2
            ((hmem_not j ka).mp hu) ((hmem_not j kb).mp hvI)
        · -- SWITCH internal edge
          split_ifs at h2 with hu1 hv1
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
          let i : Fin m := ⟨(u.val - (1 + 6 * n)) / 7, by have := u.isLt; dsimp [totalN] at this; omega⟩
          let ka : Fin 7 := ⟨(u.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
          let kb : Fin 7 := ⟨(v.val - (1 + 6 * n)) % 7, Nat.mod_lt _ (by omega)⟩
          have hueq : u = swV n m i ka := Fin.ext (by dsimp [swV, i, ka]; omega)
          have hveq : v = swV n m i kb := Fin.ext (by dsimp [swV, i, kb]; omega)
          rw [hueq] at hu; rw [hveq] at hvI
          exact swValid_no_edge _ _ (s i) ka kb (hs i) h2.2
            ((hmem_sw i ka).mp hu) ((hmem_sw i kb).mp hvI)
        · -- Cross edge: u = swV i 0, v = hub or litV i j
          split_ifs at h3 with hu1
          let i : Fin m := ⟨(u.val - (1 + 6 * n)) / 7, by have := u.isLt; dsimp [totalN] at this; omega⟩
          have hueq : u = swV n m i 0 := Fin.ext (by dsimp [swV, i]; omega)
          rw [hueq] at hu
          have hs0 : s i 0 = true := (hmem_sw i 0).mp hu
          have hsi := hs i
          dsimp only [swValid] at hsi
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hsi
          have hblk := hsi.1.1.1.1.1.1.1.1
          have hbf : blockedBit n m word hBit x negB i = false := by
            rcases hblk with hb | h0f
            · exact hb
            · rw [hs0] at h0f; cases h0f
          dsimp only [blockedBit] at hbf
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hbf
          simp only [Bool.or_eq_true, decide_eq_true_eq] at h3
          rcases h3 with rfl | ⟨j, rfl⟩
          · have hh := hmem_hub.mp hvI; rw [hbf.1] at hh; cases hh
          · dsimp only [litV] at hvI
            cases hw : word i j
            · rw [hw] at hvI; simp only [Bool.false_eq_true, ↓reduceIte] at hvI
              have hxj : x j = true := (hmem_not j 0).mp hvI
              exact hbf.2 ⟨j, by simp [hw, hxj]⟩
            · rw [hw] at hvI; simp only [↓reduceIte] at hvI
              have hnj : negB j = true := (hmem_not j 1).mp hvI
              exact hbf.2 ⟨j, by simp [hw, hnj]⟩
        · -- Cross edge: v = swV i 0, u = hub or litV i j
          split_ifs at h4 with hv1
          let i : Fin m := ⟨(v.val - (1 + 6 * n)) / 7, by have := v.isLt; dsimp [totalN] at this; omega⟩
          have hveq : v = swV n m i 0 := Fin.ext (by dsimp [swV, i]; omega)
          rw [hveq] at hvI
          have hs0 : s i 0 = true := (hmem_sw i 0).mp hvI
          have hsi := hs i
          dsimp only [swValid] at hsi
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hsi
          have hblk := hsi.1.1.1.1.1.1.1.1
          have hbf : blockedBit n m word hBit x negB i = false := by
            rcases hblk with hb | h0f
            · exact hb
            · rw [hs0] at h0f; cases h0f
          dsimp only [blockedBit] at hbf
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hbf
          simp only [Bool.or_eq_true, decide_eq_true_eq] at h4
          rcases h4 with rfl | ⟨j, rfl⟩
          · have hh := hmem_hub.mp hu; rw [hbf.1] at hh; cases hh
          · dsimp only [litV] at hu
            cases hw : word i j
            · rw [hw] at hu; simp only [Bool.false_eq_true, ↓reduceIte] at hu
              have hxj : x j = true := (hmem_not j 0).mp hu
              exact hbf.2 ⟨j, by simp [hw, hxj]⟩
            · rw [hw] at hu; simp only [↓reduceIte] at hu
              have hnj : negB j = true := (hmem_not j 1).mp hu
              exact hbf.2 ⟨j, by simp [hw, hnj]⟩
      · apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq]; exact hmem_hub
      · funext j; apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq]; exact hmem_not j 1
    · apply Prod.ext
      · funext j k; dsimp only [toPair]
        apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq]
        have h := hmem_not j ⟨k.val + 2, by omega⟩
        fin_cases k <;> exact h
      · funext i k; dsimp only [toPair]
        apply Bool.eq_iff_iff.mpr; rw [decide_eq_true_eq]
        exact hmem_sw i k

private lemma prod_mod2_eq {α : Type*} [Fintype α] (g : α → Nat) :
    (∏ a : α, g a) % 2 = if ∀ a : α, g a % 2 = 1 then 1 else 0 := by
  classical
  have hgen : ∀ (s : Finset α), (∏ a ∈ s, g a) % 2 = if ∀ a ∈ s, g a % 2 = 1 then 1 else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Nat.mul_mod, ih]
      have hmod : g a % 2 = 0 ∨ g a % 2 = 1 := by omega
      by_cases hs : ∀ b ∈ s, g b % 2 = 1
      · rcases hmod with h0 | h1
        · have hall : ¬ ∀ b ∈ insert a s, g b % 2 = 1 := fun h => by
            have := h a (Finset.mem_insert_self a s); omega
          rw [ite_eq_left hs, ite_eq_right hall, h0]
        · have hall : ∀ b ∈ insert a s, g b % 2 = 1 := by
            intro b hb; rcases Finset.mem_insert.mp hb with rfl | hb'; exact h1; exact hs b hb'
          rw [ite_eq_left hs, ite_eq_left hall, h1]
      · have hall : ¬ ∀ b ∈ insert a s, g b % 2 = 1 := fun h =>
          hs (fun b hb => h b (Finset.mem_insert_of_mem hb))
        rw [ite_eq_right hs, ite_eq_right hall]; simp
  simpa using hgen Finset.univ

private lemma main_count_mod2 (n m : Nat) (word : Fin m → Fin n → Bool)
    (f : Fin m → Bool) (x : Fin n → Bool) :
    (validISSet n m word f x).card % 2 = 1 ↔
    ∃ i : Fin m, word i = x ∧ f i = true := by
  classical
  let key : Finset (Fin (totalN n m)) → Bool × (Fin n → Bool) := fun I =>
    (decide (hubV n m ∈ I), fun j => decide (negV n m j ∈ I))
  have hsum : (validISSet n m word f x).card =
      ∑ p : Bool × (Fin n → Bool),
        (∏ j : Fin n, notCount (x j) (p.2 j)) *
        (∏ i : Fin m, swCount (blockedBit n m word p.1 x p.2 i) (f i)) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := key) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hfilt : ((validISSet n m word f x).filter (fun I => key I = p)) =
        fiberISSet n m word f x p.1 p.2 := by
      ext I; rw [Finset.mem_filter, mem_validISSet, mem_fiberISSet]
      simp [key, Prod.ext_iff]
    rw [hfilt]
    exact fiber_card_is n m word f x p.1 p.2
  rw [hsum, Finset.sum_nat_mod]
  let goodNeg : Fin n → Bool := fun j => !(x j)
  have hterm : ∀ p : Bool × (Fin n → Bool),
      ((∏ j : Fin n, notCount (x j) (p.2 j)) *
       (∏ i : Fin m, swCount (blockedBit n m word p.1 x p.2 i) (f i))) % 2 =
      if p.2 = goodNeg then
        if p.1 = true then 1
        else if ∃ i : Fin m, word i = x ∧ f i = true then 0 else 1
      else 0 := by
    rintro ⟨hb, nb⟩
    rw [Nat.mul_mod, prod_mod2_eq, prod_mod2_eq]
    by_cases hnb : nb = goodNeg
    · subst hnb
      have hnot1 : ∀ j : Fin n, notCount (x j) (goodNeg j) % 2 = 1 := by
        intro j; rw [notCount_mod2]; simp [goodNeg]
      simp only [hnot1, forall_true_left, ↓reduceIte, one_mul]
      cases hb
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hsw_iff : (∀ i : Fin m, swCount (blockedBit n m word false x goodNeg i) (f i) % 2 = 1) ↔
            ¬ ∃ i : Fin m, word i = x ∧ f i = true := by
          have hblk_eq : ∀ i : Fin m, blockedBit n m word false x goodNeg i = false ↔ word i = x := by
            intro i
            dsimp only [blockedBit, goodNeg]
            simp only [Bool.false_or, decide_eq_false_iff_not, not_exists]
            constructor
            · intro hall; funext j
              have hj := hall j
              cases hw : word i j <;> cases hx : x j <;> simp_all
            · intro heq j; rw [heq]; cases x j <;> simp
          constructor
          · rintro hall ⟨i, hwi, hfi⟩
            have h := hall i
            rw [swCount_mod2, (hblk_eq i).mpr hwi] at h
            simp [hfi] at h
          · intro hno i
            rw [swCount_mod2]
            by_cases hfi : f i = true
            · have hne : blockedBit n m word false x goodNeg i ≠ false := fun hb0 =>
                hno ⟨i, (hblk_eq i).mp hb0, hfi⟩
              simp [hne]
            · simp [hfi]
        by_cases hex : ∃ i : Fin m, word i = x ∧ f i = true
        · have hnf : ¬ ∀ i : Fin m, swCount (blockedBit n m word false x goodNeg i) (f i) % 2 = 1 :=
            fun h => hsw_iff.mp h hex
          simp [hex, hnf]
        · have hf : ∀ i : Fin m, swCount (blockedBit n m word false x goodNeg i) (f i) % 2 = 1 :=
            hsw_iff.mpr hex
          simp [hex, hf]
      · simp only [↓reduceIte]
        have hsw1 : ∀ i : Fin m, swCount (blockedBit n m word true x goodNeg i) (f i) % 2 = 1 := by
          intro i; rw [swCount_mod2]; simp [blockedBit]
        simp [hsw1]
    · have hnot0 : ¬ ∀ j : Fin n, notCount (x j) (nb j) % 2 = 1 := by
        intro hall
        apply hnb; funext j
        have h := hall j; rw [notCount_mod2] at h
        by_cases heq : nb j = !(x j)
        · exact heq
        · simp [heq] at h
      simp [hnb, hnot0]
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Bool.false_eq_true]
  by_cases hex : ∃ i : Fin m, word i = x ∧ f i = true <;> simp [hex]

/-! ### Main Body (clean context) and Bridge -/

private lemma main_body (n m : Nat) (word : Fin m → Fin n → Bool) :
    totalN n m ≤ 6 * n + (n + 7) * m + 1 ∧
    Function.Injective (pinV n m) ∧ Function.Injective (switchV n m) ∧
    (∀ j i, pinV n m j ≠ switchV n m i) ∧ (∀ j, shoreFn n m (pinV n m j) = false) ∧
    (∀ i, (graphG n m word (switchV n m i)).card = 1) ∧
    (∀ v, v ∉ graphG n m word v) ∧
    (∀ u v, v ∈ graphG n m word u ↔ u ∈ graphG n m word v) ∧
    (∀ u, ∀ v ∈ graphG n m word u, shoreFn n m v ≠ shoreFn n m u) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [totalN]; have : 7 * m ≤ (n + 7) * m := Nat.mul_le_mul_right m (by omega); omega
  · intro j1 j2 h; have := congrArg Fin.val h; dsimp [pinV, notV] at this; exact Fin.ext (by omega)
  · intro i1 i2 h; have := congrArg Fin.val h; dsimp [switchV, swV] at this; exact Fin.ext (by omega)
  · intro j i h; have := congrArg Fin.val h; dsimp [pinV, notV, switchV, swV] at this; have := j.isLt; omega
  · exact shoreFn_pinV n m
  · exact switch_deg_one n m word
  · intro v; simp [graphG, adjBool_irrefl]
  · intro u v; simp only [graphG, Finset.mem_filter, Finset.mem_univ, true_and]; rw [adjBool_symm]
  · intro u v hv; simp only [graphG, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact adjBool_bip n m word u v hv

theorem main_proof :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (n m : Nat) (word : Fin m → Fin n → Bool), Function.Injective word →
      ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (shore : Fin N → Bool)
        (pin : Fin n → Fin N) (switch : Fin m → Fin N),
        N ≤ 6*n+(n+7)*m+1 ∧ Function.Injective pin ∧ Function.Injective switch ∧
        (∀ j i, pin j ≠ switch i) ∧ (∀ j, shore (pin j) = false) ∧
        (∀ i, (G (switch i)).card = 1) ∧ (∀ v, v ∉ G v) ∧
        (∀ u v, v ∈ G u ↔ u ∈ G v) ∧ (∀ u, ∀ v ∈ G u, shore v ≠ shore u) ∧
        (∃ (h : Nat) (bag : Fin h → Finset (Fin N)), (∀ t, (bag t).card ≤ 2*n+7) ∧
          (∀ t j, pin j ∈ bag t) ∧ (∀ v, ∃ t, v ∈ bag t) ∧
          (∀ u v, v ∈ G u → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
          ∀ v s t u, s ≤ t → t ≤ u → v ∈ bag s → v ∈ bag u → v ∈ bag t) ∧
        ∀ (f : Fin m → Bool) (x : Fin n → Bool),
          let live := fun v => ∀ i, v = switch i → f i = false
          let count := ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
            (∀ v ∈ I, live v) ∧ (∀ j, pin j ∈ I ↔ x j = true) ∧
            ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card
          count % 2 = 1 ↔ ∃ i, word i = x ∧ f i = true := by
  let _ : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro n m word _hinj
  rcases main_body n m word with ⟨hN, hpin_inj, hsw_inj, hdisj, hsh, hdeg, hirr, hsym, hbip⟩
  refine ⟨totalN n m, graphG n m word, shoreFn n m, pinV n m, switchV n m,
    hN, hpin_inj, hsw_inj, hdisj, hsh, hdeg, hirr, hsym, hbip, exists_path_decomp n m word,
    fun f x => ?_⟩
  intro live count
  have hceq : count = (validISSet n m word f x).card := by
    dsimp only [count]
    apply congrArg Finset.card
    ext I
    rw [Finset.mem_filter, mem_validISSet]
    simp only [Finset.mem_univ, true_and, isValidIS, live]
  rw [hceq]
  exact main_count_mod2 n m word f x

end PEqualNP.Outside.L_lib_1231

theorem PEqualNP.Outside.L_lib_1231 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m : Nat) (word : Fin m → Fin n → Bool), Function.Injective word →
  ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (shore : Fin N → Bool)
    (pin : Fin n → Fin N) (switch : Fin m → Fin N),
    N ≤ 6*n+(n+7)*m+1 ∧ Function.Injective pin ∧ Function.Injective switch ∧
    (∀ j i, pin j ≠ switch i) ∧ (∀ j, shore (pin j) = false) ∧
    (∀ i, (G (switch i)).card = 1) ∧ (∀ v, v ∉ G v) ∧
    (∀ u v, v ∈ G u ↔ u ∈ G v) ∧ (∀ u, ∀ v ∈ G u, shore v ≠ shore u) ∧
    (∃ (h : Nat) (bag : Fin h → Finset (Fin N)), (∀ t, (bag t).card ≤ 2*n+7) ∧
      (∀ t j, pin j ∈ bag t) ∧ (∀ v, ∃ t, v ∈ bag t) ∧
      (∀ u v, v ∈ G u → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
      ∀ v s t u, s ≤ t → t ≤ u → v ∈ bag s → v ∈ bag u → v ∈ bag t) ∧
    ∀ (f : Fin m → Bool) (x : Fin n → Bool),
      let live := fun v => ∀ i, v = switch i → f i = false
      let count := ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
        (∀ v ∈ I, live v) ∧ (∀ j, pin j ∈ I ↔ x j = true) ∧
        ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card
      count % 2 = 1 ↔ ∃ i, word i = x ∧ f i = true :=
  PEqualNP.Outside.L_lib_1231.main_proof
