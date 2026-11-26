import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19137

inductive Trace (base : List ℕ) : List ℕ → Prop where
  | empty : Trace base []
  | extend {ws : List ℕ} {a b : ℕ} (previous : Trace base ws)
      (ha : a ∈ base ++ ws) (hb : b ∈ base ++ ws)
      (fresh : a ||| b ∉ base ++ ws) : Trace base (ws ++ [a ||| b])

theorem Trace.push {base ws : List ℕ} {a b : ℕ} (h : Trace base ws)
    (ha : a ∈ base ++ ws) (hb : b ∈ base ++ ws) :
    ∃ ws', Trace base ws' ∧ ws'.length ≤ ws.length + 1 ∧
      (∀ v ∈ base ++ ws, v ∈ base ++ ws') ∧ a ||| b ∈ base ++ ws' := by
  by_cases hm : a ||| b ∈ base ++ ws
  · exact ⟨ws, h, by omega, fun _ hv => hv, hm⟩
  · refine ⟨ws ++ [a ||| b], Trace.extend h ha hb hm, by simp, ?_, ?_⟩
    · intro v hv
      exact by simpa only [← List.append_assoc] using List.mem_append_left [a ||| b] hv
    · simp

theorem Trace.fresh {base ws : List ℕ} (h : Trace base ws) :
    ∀ v ∈ ws, v ∉ base := by
  induction h with
  | empty => simp
  | extend _ _ _ hf ih =>
      intro v hv hvbase
      rcases List.mem_append.mp hv with hv | hv
      · exact ih v hv hvbase
      · have e := List.mem_singleton.mp hv
        exact hf (e ▸ List.mem_append_left _ hvbase)

theorem Trace.nodup {base ws : List ℕ} (h : Trace base ws) : ws.Nodup := by
  induction h with
  | empty => simp
  | extend _ _ _ hf ih =>
      rw [List.nodup_append_comm]
      exact List.nodup_cons.mpr ⟨fun hv => hf (List.mem_append_right _ hv), ih⟩

theorem Trace.realizes {base ws : List ℕ} (h : Trace base ws) :
    ∀ i : Fin ws.length, ∃ a ∈ base ++ ws.take i.val,
      ∃ b ∈ base ++ ws.take i.val, ws.get i = a ||| b := by
  induction h with
  | empty => intro i; exact Fin.elim0 i
  | @extend old a b _ ha hb _ ih =>
      intro i
      by_cases hi : i.val < old.length
      · obtain ⟨p, hp, q, hq, he⟩ := ih ⟨i.val, hi⟩
        simp only [List.take_append_of_le_length (Nat.le_of_lt hi)]
        refine ⟨p, hp, q, hq, ?_⟩
        simpa only [List.get_eq_getElem, List.getElem_append_left hi] using he
      · have ie : i.val = old.length := by
          have il := i.isLt
          simp only [List.length_append, List.length_singleton] at il
          omega
        rw [ie, List.take_append_length]
        refine ⟨a, ha, b, hb, ?_⟩
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (by omega : old.length ≤ i.val)]
        simp [ie]

def foldPairs (s : ℕ) (xs : List (ℕ × ℕ)) : ℕ :=
  xs.foldl (fun a p => a ||| (p.1 &&& p.2)) s

theorem fold_perm {xs ys : List (ℕ × ℕ)} (h : xs.Perm ys) (z : ℕ) :
    foldPairs z xs = foldPairs z ys := by
  unfold foldPairs
  apply h.foldl_eq' _ z
  intro p _ q _ a
  rw [Nat.lor_assoc, Nat.lor_assoc, Nat.lor_comm (p.1 &&& p.2)]

theorem and_or (a b c : ℕ) : a &&& (b ||| c) = (a &&& b) ||| (a &&& c) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases a.testBit i <;> rfl

theorem zero_merge {a b c mask : ℕ} (hb : a &&& b &&& mask = 0)
    (hc : a &&& c &&& mask = 0) : a &&& (b ||| c) &&& mask = 0 := by
  rw [and_or, Nat.land_comm ((a &&& b) ||| (a &&& c)), and_or,
    Nat.land_comm mask (a &&& b), Nat.land_comm mask (a &&& c), hb, hc]
  rfl

def keys (ps : List (ℕ × ℕ)) : Finset ℕ :=
  (ps.map Prod.fst).toFinset

@[simp] theorem keys_cons (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) :
    keys (p :: ps) = insert p.1 (keys ps) := by
  simp [keys]

theorem keys_perm {xs ys : List (ℕ × ℕ)} (h : xs.Perm ys) : keys xs = keys ys := by
  ext a
  simpa only [keys, List.mem_toFinset] using ((h.map Prod.fst).mem_iff (a := a))

structure Grouped (base : List ℕ) (mask : ℕ) (ps : List (ℕ × ℕ))
    (ws : List ℕ) (out : List (ℕ × ℕ)) : Prop where
  trace : Trace base ws
  sameKeys : keys out = keys ps
  groups : out.length = (keys ps).card
  budget : ws.length + out.length ≤ ps.length
  valid : ∀ p ∈ out, p.1 ∈ base ++ ws ∧ p.2 ∈ base ++ ws ∧ p.1 &&& p.2 &&& mask = 0
  sameValue : ∀ z, foldPairs z out = foldPairs z ps

theorem group (base : List ℕ) (mask : ℕ) (ps : List (ℕ × ℕ))
    (hps : ∀ p ∈ ps, p.1 ∈ base ∧ p.2 ∈ base ∧ p.1 &&& p.2 &&& mask = 0) :
    ∃ ws out, Grouped base mask ps ws out := by
  induction ps with
  | nil =>
      exact ⟨[], [], Trace.empty, rfl, by simp [keys], by simp, by simp, fun _ => rfl⟩
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      obtain ⟨ha, hb, hzero⟩ := hps (a,b) (List.mem_cons_self ..)
      obtain ⟨ws, out, h⟩ := ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))
      have hA : a ∈ base ++ ws := List.mem_append_left _ ha
      have hB : b ∈ base ++ ws := List.mem_append_left _ hb
      by_cases old : a ∈ out.map Prod.fst
      · obtain ⟨⟨a', c⟩, hc, hfst⟩ := List.mem_map.mp old
        change a' = a at hfst
        subst a'
        let rest := out.erase (a,c)
        have hp : out.Perm ((a,c) :: rest) := List.perm_cons_erase hc
        have hl : out.length = rest.length + 1 := by simpa using hp.length_eq
        have hka : a ∈ keys ps := by
          rw [← h.sameKeys]
          simpa only [keys, List.mem_toFinset] using old
        have hz := h.valid (a,c) hc
        obtain ⟨ws',ht,hgrow,hsub,hbc⟩ := h.trace.push hB hz.2.1
        refine ⟨ws', (a,b ||| c) :: rest, ht, ?_, ?_, ?_, ?_, ?_⟩
        · rw [keys_cons, keys_cons, Finset.insert_eq_of_mem hka]
          calc
            insert a (keys rest) = keys out := by simpa only [keys_cons] using (keys_perm hp).symm
            _ = keys ps := h.sameKeys
        · simp only [List.length_cons, keys_cons, Finset.insert_eq_of_mem hka]
          have hc := h.groups
          omega
        · simp only [List.length_cons]
          have oldBudget := h.budget
          omega
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hsub _ hA, hbc, zero_merge hzero hz.2.2⟩
          · have hx' : x ∈ out := hp.symm.subset (List.mem_cons_of_mem _ hx)
            obtain ⟨x₁,x₂,zero⟩ := h.valid x hx'
            exact ⟨hsub _ x₁, hsub _ x₂, zero⟩
        · intro z
          have hf := fold_perm hp (z ||| (a &&& b))
          have he := h.sameValue (z ||| (a &&& b))
          change foldPairs (z ||| (a &&& (b ||| c))) rest = foldPairs (z ||| (a &&& b)) ps
          rw [and_or, ← Nat.lor_assoc]
          exact hf.symm.trans he
      · have hna : a ∉ keys ps := by
          rw [← h.sameKeys]
          simpa only [keys, List.mem_toFinset] using old
        refine ⟨ws, (a,b) :: out, h.trace, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [keys_cons, h.sameKeys]
        · simp only [List.length_cons, keys_cons, Finset.card_insert_of_notMem hna, h.groups]
        · simp only [List.length_cons]
          have oldBudget := h.budget
          omega
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hA, hB, hzero⟩
          · exact h.valid x hx
        · intro z
          exact h.sameValue _

end PEqualNP.Outside.L_meta_19137

open PEqualNP.Outside.L_meta_19137 in
theorem PEqualNP.Outside.L_meta_19137 :
    ∀ (x1 : List ℕ) (x2 : List (ℕ × ℕ)) (x3 x4 : ℕ),   x2 ≠ [] →     (∀ x6 ∈ x2, x6.1 ∈ x1 ∧ x6.2 ∈ x1 ∧ x6.1 &&& x6.2 &&& x3 = (0 : ℕ)) →       ∃ (x7 : List ℕ) (x8 : List (ℕ × ℕ)),         x7.Nodup ∧           (∀ x9 ∈ x7, x9 ∉ x1) ∧             x8 ≠ [] ∧               x7.length + (2 : ℕ) * x8.length ≤ x2.length + (List.map Prod.fst x2).toFinset.card ∧                 (∀ (x9 : Fin x7.length),                     have x10 : List ℕ := x1 ++ List.take (↑x9) x7;                     ∃ x11 ∈ x10, ∃ x12 ∈ x10, x7.get x9 = x11 ||| x12) ∧                   (∀ x9 ∈ x8, x9.1 ∈ x1 ++ x7 ∧ x9.2 ∈ x1 ++ x7 ∧ x9.1 &&& x9.2 &&& x3 = (0 : ℕ)) ∧ List.foldl (fun (x9 : ℕ) (x10 : ℕ × ℕ) => x9 ||| x10.1 &&& x10.2) x4 x8 = List.foldl (fun (x9 : ℕ) (x10 : ℕ × ℕ) => x9 ||| x10.1 &&& x10.2) x4 x2 := by
  intro base ps mask seed hp hvalid
  obtain ⟨ws, out, g⟩ := group base mask ps hvalid
  have keyCount : out.length = (List.map Prod.fst ps).toFinset.card := g.groups
  have budget := g.budget
  have outNE : out ≠ [] := by
    intro he
    have hz : keys ps = ∅ := by
      rw [← g.sameKeys, he]
      rfl
    have hn : ps.map Prod.fst = [] := (List.toFinset_eq_empty_iff _).mp hz
    exact hp (List.map_eq_nil_iff.mp hn)
  exact ⟨ws, out, g.trace.nodup, g.trace.fresh, outNE, by omega,
    g.trace.realizes, g.valid, g.sameValue seed⟩
