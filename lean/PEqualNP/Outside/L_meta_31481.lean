import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31481

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section Prog
variable {ι κ : Type}

def K (S : (ι → Bool) → Prop) (w : ι → Bool) : Prop :=
  (∃ c : Bool, w = fun _ => c) ∨ S w ∨ S (fun x => !w x)

def ins (z : ι → Bool) (S : (ι → Bool) → Prop) : (ι → Bool) → Prop := fun w => w = z ∨ S w

def Run : ℕ → ((ι → Bool) → Prop) → (ι → Bool) → Prop
  | 0, S, f => K S f
  | t + 1, S, f => Run t S f ∨
      ∃ a b : ι → Bool, K S a ∧ K S b ∧ Run t (ins (fun x => a x && b x) S) f

theorem K_not {S : (ι → Bool) → Prop} {w : ι → Bool} (h : K S w) : K S (fun x => !w x) := by
  rcases h with ⟨c, rfl⟩ | h | h
  · exact Or.inl ⟨!c, rfl⟩
  · exact Or.inr (Or.inr (by simpa using h))
  · exact Or.inr (Or.inl h)

theorem K_ins {S : (ι → Bool) → Prop} {z w : ι → Bool} (h : K S w) : K (ins z S) w := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem K_new {S : (ι → Bool) → Prop} (z : ι → Bool) : K (ins z S) z := Or.inr (Or.inl (Or.inl rfl))

theorem K_and {S : (ι → Bool) → Prop} {a b : ι → Bool} (ha : ∃ c, ∀ y, a y = c) (hb : K S b) :
    K S (fun y => a y && b y) := by
  obtain ⟨c, hc⟩ := ha
  cases c
  · exact Or.inl ⟨false, funext fun y => by simp [hc y]⟩
  · have : (fun y => a y && b y) = b := funext fun y => by simp [hc y]
    rw [this]; exact hb

theorem K_bind {S : (ι → Bool) → Prop} {S' : (κ → Bool) → Prop} (σ : κ → ι)
    (h : ∀ w, S w → K S' (fun y => w (σ y))) {w : ι → Bool} (hw : K S w) :
    K S' (fun y => w (σ y)) := by
  rcases hw with ⟨c, rfl⟩ | hw | hw
  · exact Or.inl ⟨c, rfl⟩
  · exact h w hw
  · have h2 := K_not (h _ hw)
    simpa using h2

theorem Run_map (σ : κ → ι) : ∀ (t : ℕ) (S : (ι → Bool) → Prop) (S' : (κ → Bool) → Prop)
    (f : ι → Bool), (∀ w, S w → K S' (fun y => w (σ y))) → Run t S f → Run t S' (fun y => f (σ y))
  | 0, _, _, _, h, hf => K_bind σ h hf
  | t + 1, S, S', f, h, hf => by
    rcases hf with hf | ⟨a, b, ha, hb, hf⟩
    · exact Or.inl (Run_map σ t S S' f h hf)
    · refine Or.inr ⟨_, _, K_bind σ h ha, K_bind σ h hb, Run_map σ t _ _ f ?_ hf⟩
      rintro w (rfl | hw)
      · exact K_new _
      · exact K_ins (h w hw)

theorem Run_le {t t' : ℕ} {S : (ι → Bool) → Prop} {f : ι → Bool} (h : t ≤ t') (hf : Run t S f) :
    Run t' S f := by
  induction h with
  | refl => exact hf
  | step _ ih => exact Or.inl ih

def Cl (σ : κ → ι) (p q r : ι) (S : (ι → Bool) → Prop) : Prop :=
  ∀ w, S w → w p ≠ w q → ∀ y, w (σ y) = w r

theorem Cl_K {σ : κ → ι} {p q r : ι} {S : (ι → Bool) → Prop} (h : Cl σ p q r S) {w : ι → Bool}
    (hw : K S w) (hd : w p ≠ w q) (y : κ) : w (σ y) = w r := by
  rcases hw with ⟨c, rfl⟩ | hw | hw
  · exact absurd rfl hd
  · exact h w hw hd y
  · have h2 := h _ hw (by simpa using hd) y
    simpa using h2

theorem and_dep {a b : ι → Bool} {p q : ι} (h : (a p && b p) ≠ (a q && b q)) :
    a p ≠ a q ∨ b p ≠ b q := by
  by_contra hc
  simp only [not_or, not_not] at hc
  exact h (by rw [hc.1, hc.2])

theorem kill1 (σ : κ → ι) (p q r : ι) : ∀ (t : ℕ) (S : (ι → Bool) → Prop) (S' : (κ → Bool) → Prop)
    (f : ι → Bool), Cl σ p q r S → (∀ w, S w → K S' (fun y => w (σ y))) → f p ≠ f q →
    (∃ y y', f (σ y) ≠ f (σ y')) → Run t S f → ∃ t', t' + 1 ≤ t ∧ Run t' S' (fun y => f (σ y))
  | 0, _, _, f, hc, _, hd, ⟨y, y', hn⟩, hf =>
    absurd ((Cl_K hc hf hd y).trans (Cl_K hc hf hd y').symm) hn
  | t + 1, S, S', f, hc, hm, hd, hn, hf => by
    rcases hf with hf | ⟨a, b, ha, hb, hf⟩
    · obtain ⟨t', ht, hr⟩ := kill1 σ p q r t S S' f hc hm hd hn hf
      exact ⟨t', by omega, hr⟩
    · by_cases hz : (a p && b p) ≠ (a q && b q)
      · have hk : K S' (fun y => a (σ y) && b (σ y)) := by
          rcases and_dep hz with h | h
          · exact K_and ⟨a r, Cl_K hc ha h⟩ (K_bind σ hm hb)
          · have e : (fun y => a (σ y) && b (σ y)) = fun y => b (σ y) && a (σ y) :=
              funext fun y => Bool.and_comm _ _
            rw [e]
            exact K_and ⟨b r, Cl_K hc hb h⟩ (K_bind σ hm ha)
        refine ⟨t, le_rfl, Run_map σ t _ S' f ?_ hf⟩
        rintro w (rfl | hw)
        · exact hk
        · exact hm w hw
      · obtain ⟨t', ht, hr⟩ := kill1 σ p q r t (ins (fun x => a x && b x) S)
          (ins (fun y => a (σ y) && b (σ y)) S') f
          (by
            rintro w (rfl | hw) hd2
            · exact absurd hd2 hz
            · exact hc w hw hd2)
          (by
            rintro w (rfl | hw)
            · exact K_new _
            · exact K_ins (hm w hw)) hd hn hf
        exact ⟨t' + 1, by omega, Or.inr ⟨_, _, K_bind σ hm ha, K_bind σ hm hb, hr⟩⟩

theorem kill2_dep (σ0 σ1 : κ → ι) (p q : ι) {t : ℕ} {S : (ι → Bool) → Prop}
    {S0 S1 : (κ → Bool) → Prop} {f a b : ι → Bool} (hc0 : Cl σ0 p q p S) (hc1 : Cl σ1 p q q S)
    (hm0 : ∀ w, S w → K S0 (fun y => w (σ0 y))) (hm1 : ∀ w, S w → K S1 (fun y => w (σ1 y)))
    (hd : f p ≠ f q) (hn0 : ∃ y y', f (σ0 y) ≠ f (σ0 y')) (hn1 : ∃ y y', f (σ1 y) ≠ f (σ1 y'))
    (ha : K S a) (hb : K S b) (hda : a p ≠ a q) (hf : Run t (ins (fun x => a x && b x) S) f) :
    ∃ t0 t1, Run t0 S0 (fun y => f (σ0 y)) ∧ Run t1 S1 (fun y => f (σ1 y)) ∧
      ((t0 + 2 ≤ t + 1 ∧ t1 + 1 ≤ t + 1) ∨ (t0 + 1 ≤ t + 1 ∧ t1 + 2 ≤ t + 1)) := by
  have k0 := Cl_K hc0 ha hda
  have k1 := Cl_K hc1 ha hda
  have hz0 : ∀ w, ins (fun x => a x && b x) S w → K S0 (fun y => w (σ0 y)) := by
    rintro w (rfl | hw)
    · exact K_and ⟨_, k0⟩ (K_bind σ0 hm0 hb)
    · exact hm0 w hw
  have hz1 : ∀ w, ins (fun x => a x && b x) S w → K S1 (fun y => w (σ1 y)) := by
    rintro w (rfl | hw)
    · exact K_and ⟨_, k1⟩ (K_bind σ1 hm1 hb)
    · exact hm1 w hw
  cases hap : a p
  · obtain ⟨t', ht, hr⟩ := kill1 σ0 p q p t _ S0 f (by
        rintro w (rfl | hw) hd2
        · intro y; simp [k0 y, hap]
        · exact hc0 w hw hd2) hz0 hd hn0 hf
    exact ⟨t', t, hr, Run_map σ1 t _ S1 f hz1 hf, Or.inl ⟨by omega, le_rfl⟩⟩
  · have haq : a q = false := by
      cases h : a q
      · rfl
      · exact absurd (hap.trans h.symm) hda
    obtain ⟨t', ht, hr⟩ := kill1 σ1 p q q t _ S1 f (by
        rintro w (rfl | hw) hd2
        · intro y; simp [k1 y, haq]
        · exact hc1 w hw hd2) hz1 hd hn1 hf
    exact ⟨t, t', Run_map σ0 t _ S0 f hz0 hf, hr, Or.inr ⟨le_rfl, by omega⟩⟩

theorem kill2 (σ0 σ1 : κ → ι) (p q : ι) : ∀ (t : ℕ) (S : (ι → Bool) → Prop)
    (S0 S1 : (κ → Bool) → Prop) (f : ι → Bool), Cl σ0 p q p S → Cl σ1 p q q S →
    (∀ w, S w → K S0 (fun y => w (σ0 y))) → (∀ w, S w → K S1 (fun y => w (σ1 y))) → f p ≠ f q →
    (∃ y y', f (σ0 y) ≠ f (σ0 y')) → (∃ y y', f (σ1 y) ≠ f (σ1 y')) → Run t S f →
    ∃ t0 t1, Run t0 S0 (fun y => f (σ0 y)) ∧ Run t1 S1 (fun y => f (σ1 y)) ∧
      ((t0 + 2 ≤ t ∧ t1 + 1 ≤ t) ∨ (t0 + 1 ≤ t ∧ t1 + 2 ≤ t))
  | 0, _, _, _, f, hc, _, _, _, hd, ⟨y, y', hn⟩, _, hf =>
    absurd ((Cl_K hc hf hd y).trans (Cl_K hc hf hd y').symm) hn
  | t + 1, S, S0, S1, f, hc0, hc1, hm0, hm1, hd, hn0, hn1, hf => by
    rcases hf with hf | ⟨a, b, ha, hb, hf⟩
    · obtain ⟨t0, t1, r0, r1, h⟩ := kill2 σ0 σ1 p q t S S0 S1 f hc0 hc1 hm0 hm1 hd hn0 hn1 hf
      exact ⟨t0, t1, r0, r1, by omega⟩
    · by_cases hz : (a p && b p) ≠ (a q && b q)
      · rcases and_dep hz with h | h
        · exact kill2_dep σ0 σ1 p q hc0 hc1 hm0 hm1 hd hn0 hn1 ha hb h hf
        · have e : (fun x => a x && b x) = fun x => b x && a x :=
            funext fun x => Bool.and_comm _ _
          rw [e] at hf
          exact kill2_dep σ0 σ1 p q hc0 hc1 hm0 hm1 hd hn0 hn1 hb ha h hf
      · obtain ⟨t0, t1, r0, r1, h⟩ := kill2 σ0 σ1 p q t (ins (fun x => a x && b x) S)
          (ins (fun y => a (σ0 y) && b (σ0 y)) S0) (ins (fun y => a (σ1 y) && b (σ1 y)) S1) f
          (by
            rintro w (rfl | hw) hd2
            · exact absurd hd2 hz
            · exact hc0 w hw hd2)
          (by
            rintro w (rfl | hw) hd2
            · exact absurd hd2 hz
            · exact hc1 w hw hd2)
          (by
            rintro w (rfl | hw)
            · exact K_new _
            · exact K_ins (hm0 w hw))
          (by
            rintro w (rfl | hw)
            · exact K_new _
            · exact K_ins (hm1 w hw)) hd hn0 hn1 hf
        exact ⟨t0 + 1, t1 + 1, Or.inr ⟨_, _, K_bind σ0 hm0 ha, K_bind σ0 hm0 hb, r0⟩,
          Or.inr ⟨_, _, K_bind σ1 hm1 ha, K_bind σ1 hm1 hb, r1⟩, by omega⟩

end Prog

section Rules
variable {n : ℕ}

abbrev BF (n : ℕ) := (Fin n → Bool) → Bool

def Vars (n : ℕ) : BF n → Prop := fun w => ∃ i : Fin n, w = fun x => x i

def LB (f : BF n) (b : ℕ) : Prop := ∀ t, Run t (Vars n) f → b ≤ t

def pt (n : ℕ) (c : ℕ) : Fin n → Bool := fun i => c.testBit i.val

def rs (f : BF n) (i : Fin n) (c : Bool) : BF n := fun x => f (Function.update x i c)

theorem vars_rs (i : Fin n) (c : Bool) (w : BF n) (hw : Vars n w) :
    K (Vars n) (fun x => w (Function.update x i c)) := by
  obtain ⟨j, rfl⟩ := hw
  by_cases h : j = i
  · subst h; exact Or.inl ⟨c, by simp⟩
  · exact Or.inr (Or.inl ⟨j, by simp [Function.update_of_ne h]⟩)

theorem vars_cl (i : Fin n) (c : Bool) (x : Fin n → Bool) :
    Cl (fun y => Function.update y i c) (Function.update x i false) (Function.update x i true)
      (Function.update x i c) (Vars n) := by
  rintro w ⟨j, rfl⟩ hd y
  by_cases h : j = i
  · subst h; simp
  · exact absurd (by simp [Function.update_of_ne h]) hd

theorem rule1 (f : BF n) (i : Fin n) (c : Bool) (b p y y' : ℕ)
    (hd : f (Function.update (pt n p) i false) ≠ f (Function.update (pt n p) i true))
    (hn : rs f i c (pt n y) ≠ rs f i c (pt n y')) (h : LB (rs f i c) b) : LB f (b + 1) := by
  intro t ht
  obtain ⟨t', h1, h2⟩ := kill1 _ _ _ _ t _ (Vars n) f (vars_cl i c (pt n p)) (vars_rs i c) hd
    ⟨_, _, hn⟩ ht
  have := h t' h2
  omega

theorem rule2 (f : BF n) (i : Fin n) (b p y y' u u' : ℕ)
    (hd : f (Function.update (pt n p) i false) ≠ f (Function.update (pt n p) i true))
    (hn0 : rs f i false (pt n y) ≠ rs f i false (pt n y'))
    (hn1 : rs f i true (pt n u) ≠ rs f i true (pt n u'))
    (h0 : LB (rs f i false) b) (h1 : LB (rs f i true) b) : LB f (b + 2) := by
  intro t ht
  obtain ⟨t0, t1, r0, r1, h⟩ := kill2 _ _ _ _ t _ (Vars n) (Vars n) f (vars_cl i false (pt n p))
    (vars_cl i true (pt n p)) (vars_rs i false) (vars_rs i true) hd ⟨_, _, hn0⟩ ⟨_, _, hn1⟩ ht
  have g0 := h0 t0 r0
  have g1 := h1 t1 r1
  omega

theorem LB_mono {f : BF n} {b b' : ℕ} (h : LB f b) (hb : b' ≤ b) : LB f b' :=
  fun t ht => hb.trans (h t ht)

theorem LB_perm (π : Fin n → Fin n) (f g : BF n) (hg : ∀ x, g x = f (fun i => x (π i))) {b : ℕ}
    (h : LB g b) : LB f b := by
  intro t ht
  apply h t
  have e : g = fun x => f (fun i => x (π i)) := funext hg
  rw [e]
  refine Run_map (fun (x : Fin n → Bool) (i : Fin n) => x (π i)) t _ _ f ?_ ht
  rintro w ⟨j, rfl⟩
  exact Or.inr (Or.inl ⟨π j, rfl⟩)

end Rules

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

def ops (a b : ℕ) : List ℕ := [a &&& b, a ||| b, a ^^^ (a &&& b), b ^^^ (a &&& b)]

abbrev bops (a b : ℕ) : Finset ℕ := (ops a b).toFinset

def sep (P m x : ℕ) : ℕ := Nat.land (Nat.xor (Nat.shiftRight x P) x) m

def cuts (P m : ℕ) (ws : List ℕ) : ℕ := ws.foldr (fun w v => Nat.lor (sep P m w) v) 0

def differs (P i w : ℕ) : Prop := w.testBit (P + i) ≠ w.testBit i

theorem ops_differs (P i a b z : ℕ) (hz : z ∈ bops a b) (hd : differs P i z) :
    differs P i a ∨ differs P i b := by
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, ha, hb]

theorem mask_bit (P i : ℕ) : (2 ^ P - 1).testBit i = decide (i < P) := Nat.testBit_two_pow_sub_one P i

theorem cuts_spec (P : ℕ) (ws : List ℕ) (i : ℕ) :
    (cuts P (2 ^ P - 1) ws).testBit i = true ↔ i < P ∧ ∃ w ∈ ws, differs P i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change ((((a >>> P) ^^^ a) &&& (2 ^ P - 1)) ||| cuts P (2 ^ P - 1) rest).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, mask_bit,
      Bool.and_eq_true, bx, decide_eq_true_eq, differs, List.mem_cons, exists_eq_or_imp]
    tauto

theorem cuts_full {P g : ℕ} (hg : ∀ i, i < P → differs P i g) {k : ℕ} {ws : List ℕ}
    (h : live bops g k ws.toFinset) : cuts P (2 ^ P - 1) ws = 2 ^ P - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [mask_bit]
  by_cases hi : i < P
  · have hw := live_separates (differs P i) (hg i hi) (ops_differs P i) h
    simpa [hi] using (cuts_spec P ws i).mpr ⟨hi, by simpa using hw⟩
  · cases hb : (cuts P (2 ^ P - 1) ws).testBit i
    · simp [hi]
    · exact absurd ((cuts_spec P ws i).mp hb).1 hi

theorem ops_swap (a b : ℕ) : bops a b = bops b a := by
  ext z
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [Nat.and_comm a b, Nat.or_comm a b]
  tauto

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def keepChoices (a b : ℕ) (r : List ℕ) : List (List ℕ) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List ℕ} {a b : ℕ} {needed : Finset ℕ}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : ℕ} {ws : List ℕ} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def fz {β : Type} (n : ℕ) (f : ℕ → β) : β := Nat.casesOn n (f 0) (fun k => f (Nat.succ k))

theorem fz_eq {β : Type} (n : ℕ) (f : ℕ → β) : fz n f = f n := by cases n <;> rfl

def fzl {β : Type} : List ℕ → (List ℕ → β) → β
  | [], f => f []
  | a :: t, f => fz a fun a' => fzl t fun t' => f (a' :: t')

theorem fzl_eq {β : Type} : ∀ (l : List ℕ) (f : List ℕ → β), fzl l f = f l
  | [], f => rfl
  | a :: t, f => by simp [fzl, fz_eq, fzl_eq t]

def enc {ρ : Type} (w : ρ → Bool) : List ρ → ℕ
  | [] => 0
  | p :: t => Nat.bit (w p) (enc w t)

theorem enc_testBit {ρ : Type} (w : ρ → Bool) : ∀ (l : List ρ) (j : ℕ),
    (enc w l).testBit j = (l.map w).getD j false
  | [], j => by simp [enc]
  | p :: t, 0 => by simp [enc]
  | p :: t, j + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit w t j]

theorem enc_lt {ρ : Type} (w : ρ → Bool) (l : List ρ) : enc w l < 2 ^ l.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [enc_testBit, List.getD_eq_default _ _ (by simp; omega)]

theorem enc_congr {ρ : Type} {w w' : ρ → Bool} (h : ∀ x, w x = w' x) (l : List ρ) :
    enc w l = enc w' l := by
  have : w = w' := funext h
  rw [this]

theorem enc_false {ρ : Type} (l : List ρ) : enc (fun _ : ρ => false) l = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [enc, ih]

theorem enc_op {ρ : Type} (o : Bool → Bool → Bool) (o' : ℕ → ℕ → ℕ) (h0 : o false false = false)
    (ho : ∀ a b i, (o' a b).testBit i = o (a.testBit i) (b.testBit i)) (a b : ρ → Bool)
    (l : List ρ) : enc (fun r => o (a r) (b r)) l = o' (enc a l) (enc b l) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [ho, enc_testBit, enc_testBit, enc_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega), h0]

section Code
variable {ρ : Type} (x0 : ρ) (pts : List ρ)

def code (w : ρ → Bool) : ℕ := enc (fun x => Bool.xor (w x) (w x0)) pts

theorem code_const (c : Bool) : code x0 pts (fun _ => c) = 0 := by
  unfold code
  rw [← enc_false pts]
  exact enc_congr (fun x => by simp) pts

theorem code_not (w : ρ → Bool) : code x0 pts (fun x => !w x) = code x0 pts w :=
  enc_congr (fun x => by
    show Bool.xor (!w x) (!w x0) = Bool.xor (w x) (w x0)
    cases w x <;> cases w x0 <;> rfl) pts

theorem code_and (a b : ρ → Bool) :
    code x0 pts (fun x => a x && b x) ∈ bops (code x0 pts a) (code x0 pts b) := by
  have e1 := enc_op (ρ := ρ) (fun p q => p && q) (· &&& ·) rfl (fun a b i => Nat.testBit_and a b i)
    (fun x => Bool.xor (a x) (a x0)) (fun x => Bool.xor (b x) (b x0)) pts
  have e2 := enc_op (ρ := ρ) (fun p q => p || q) (· ||| ·) rfl (fun a b i => Nat.testBit_or a b i)
    (fun x => Bool.xor (a x) (a x0)) (fun x => Bool.xor (b x) (b x0)) pts
  have e3 := enc_op (ρ := ρ) (fun p q => Bool.xor p (p && q)) (fun a b => a ^^^ (a &&& b)) rfl
    (fun a b i => by simp [Nat.testBit_and, Nat.testBit_xor])
    (fun x => Bool.xor (a x) (a x0)) (fun x => Bool.xor (b x) (b x0)) pts
  have e4 := enc_op (ρ := ρ) (fun p q => Bool.xor q (p && q)) (fun a b => b ^^^ (a &&& b)) rfl
    (fun a b i => by simp [Nat.testBit_and, Nat.testBit_xor])
    (fun x => Bool.xor (a x) (a x0)) (fun x => Bool.xor (b x) (b x0)) pts
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  unfold code
  cases ha : a x0 <;> cases hb : b x0
  · left
    rw [ha, hb] at e1
    rw [← e1]
    exact enc_congr (fun x => by simp only [ha, hb]; cases a x <;> cases b x <;> rfl) pts
  · right; right; left
    rw [ha, hb] at e3
    rw [← e3]
    exact enc_congr (fun x => by simp only [ha, hb]; cases a x <;> cases b x <;> rfl) pts
  · right; right; right
    rw [ha, hb] at e4
    rw [← e4]
    exact enc_congr (fun x => by simp only [ha, hb]; cases a x <;> cases b x <;> rfl) pts
  · right; left
    rw [ha, hb] at e2
    rw [← e2]
    exact enc_congr (fun x => by simp only [ha, hb]; cases a x <;> cases b x <;> rfl) pts

theorem bops_zero {b z : ℕ} (hz : z ∈ bops 0 b) : z = 0 ∨ z = b := by
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp

theorem bops_self {b z : ℕ} (hz : z ∈ bops b b) : z = 0 ∨ z = b := by
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp

theorem sim (f : ρ → Bool) (hf : code x0 pts f ≠ 0) : ∀ (t : ℕ) (S : (ρ → Bool) → Prop)
    (A : Finset ℕ), (∀ w, S w → code x0 pts w = 0 ∨ code x0 pts w ∈ A) → Run t S f →
    build bops (code x0 pts f) t A
  | 0, S, A, h, hr => by
    rcases hr with ⟨c, rfl⟩ | hr | hr
    · exact absurd (code_const x0 pts c) hf
    · exact (h f hr).resolve_left hf
    · have := h _ hr
      rw [code_not] at this
      exact this.resolve_left hf
  | t + 1, S, A, h, hr => by
    rcases hr with hr | ⟨a, b, ha, hb, hr⟩
    · exact Or.inl (sim f hf t S A h hr)
    · have hK : ∀ w, K S w → code x0 pts w = 0 ∨ code x0 pts w ∈ A := by
        intro w hw
        rcases hw with ⟨c, rfl⟩ | hw | hw
        · exact Or.inl (code_const x0 pts c)
        · exact h w hw
        · have := h _ hw
          rwa [code_not] at this
      have hmem := code_and x0 pts a b
      by_cases hz : code x0 pts (fun x => a x && b x) = 0 ∨ code x0 pts (fun x => a x && b x) ∈ A
      · refine Or.inl (sim f hf t _ A ?_ hr)
        rintro w (rfl | hw)
        · exact hz
        · exact h w hw
      · have ha' := hK a ha
        have hb' := hK b hb
        have haA : code x0 pts a ∈ A := by
          rcases ha' with h0 | h1
          · rw [h0] at hmem
            rcases bops_zero hmem with e | e
            · exact absurd (Or.inl e) hz
            · exact absurd (e ▸ hb') hz
          · exact h1
        have hbA : code x0 pts b ∈ A := by
          rcases hb' with h0 | h1
          · rw [h0, ops_swap] at hmem
            rcases bops_zero hmem with e | e
            · exact absurd (Or.inl e) hz
            · exact absurd (e ▸ ha') hz
          · exact h1
        have hne : code x0 pts a ≠ code x0 pts b := by
          intro e
          rw [e] at hmem
          rcases bops_self hmem with e2 | e2
          · exact hz (Or.inl e2)
          · exact hz (Or.inr (e2 ▸ hbA))
        refine Or.inr ⟨_, haA, _, hbA, hne, _, hmem, sim f hf t _ _ ?_ hr⟩
        rintro w (rfl | hw)
        · exact Or.inr (Finset.mem_insert_self _ _)
        · exact (h w hw).imp id (fun h => Finset.mem_insert_of_mem h)

end Code

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def bc (gs : List Gate) : ℕ := (gs.filter isBinary).length

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

section Compile
variable {n : ℕ}

def rd (ws : List (BF n)) (i : ℕ) : BF n := fun x => (ws.map fun w => w x).getD i false

theorem rd_K {S : BF n → Prop} {ws : List (BF n)} (hw : ∀ w ∈ ws, K S w) (i : ℕ) :
    K S (rd ws i) := by
  by_cases h : i < ws.length
  · have : rd ws i = ws[i] := by
      funext x
      simp [rd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rw [this]
    exact hw _ (List.getElem_mem h)
  · refine Or.inl ⟨false, ?_⟩
    funext x
    simp [rd, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem gate_run {S : BF n → Prop} {ws : List (BF n)} (hw : ∀ w ∈ ws, K S w) (g : Gate)
    (hg : legal g) (z : BF n)
    (hz : z = fun x => g.op.eval (g.inputs.map fun i => rd ws i x)) :
    K S z ∨ (isBinary g = true ∧ ∃ a b : BF n, K S a ∧ K S b ∧ K (ins (fun x => a x && b x) S) z) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  subst hz
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩
  · left
    rcases hop with rfl | rfl | rfl
    · exact Or.inl ⟨true, rfl⟩
    · exact Or.inl ⟨false, rfl⟩
    · exact Or.inl ⟨true, rfl⟩
  · left
    rcases hop with rfl | rfl | rfl
    · have e : (fun x => GateOp.eval .and ([i].map fun i => rd ws i x)) = rd ws i :=
        funext fun x => by simp [GateOp.eval]
      simp only [e]; exact rd_K hw i
    · have e : (fun x => GateOp.eval .or ([i].map fun i => rd ws i x)) = rd ws i :=
        funext fun x => by simp [GateOp.eval]
      simp only [e]; exact rd_K hw i
    · exact K_not (rd_K hw i)
  · rcases hop with rfl | rfl | rfl
    · right
      refine ⟨rfl, rd ws i, rd ws j, rd_K hw i, rd_K hw j, ?_⟩
      have e : (fun x => GateOp.eval .and ([i, j].map fun i => rd ws i x)) =
          fun x => rd ws i x && rd ws j x := funext fun x => by simp [GateOp.eval]
      simp only [e]; exact K_new _
    · right
      refine ⟨rfl, _, _, K_not (rd_K hw i), K_not (rd_K hw j), ?_⟩
      have e : (fun x => GateOp.eval .or ([i, j].map fun i => rd ws i x)) =
          fun x => !(!rd ws i x && !rd ws j x) := funext fun x => by simp [GateOp.eval]
      simp only [e]; exact K_not (K_new _)
    · left
      exact K_not (rd_K hw i)
  · simp at cap

theorem compile (out : ℕ) : ∀ (gs : List Gate) (ws : List (BF n)) (S : BF n → Prop),
    (∀ g ∈ gs, legal g) → (∀ w ∈ ws, K S w) →
    Run (bc gs) S (fun x => (gs.foldl step (ws.map fun w => w x)).getD out false)
  | [], ws, S, _, hw => rd_K hw out
  | g :: gs, ws, S, hg, hw => by
    set z : BF n := fun x => g.op.eval (g.inputs.map fun i => rd ws i x) with hz
    have hst : ∀ x, step (ws.map fun w => w x) g = (ws ++ [z]).map fun w => w x := by
      intro x
      simp [step, hz, rd]
    have hfold : (fun x => ((g :: gs).foldl step (ws.map fun w => w x)).getD out false) =
        fun x => (gs.foldl step ((ws ++ [z]).map fun w => w x)).getD out false := by
      funext x
      rw [List.foldl_cons, hst x]
    rw [hfold]
    have tail := fun S' h => compile out gs (ws ++ [z]) S' (fun g' h' => hg g' (by simp [h'])) h
    have ext : ∀ S' : BF n → Prop, (∀ w ∈ ws, K S' w) → K S' z → ∀ w ∈ ws ++ [z], K S' w := by
      intro S' h1 h2 w hm
      rcases List.mem_append.mp hm with hm | hm
      · exact h1 w hm
      · exact (List.mem_singleton.mp hm) ▸ h2
    have hle : bc gs ≤ bc (g :: gs) := by
      unfold bc
      rw [List.filter_cons]
      split <;> simp
    rcases gate_run hw g (hg g (by simp)) z hz with h | ⟨hb, a, b, ha, hb2, h⟩
    · exact Run_le hle (tail S (ext S hw h))
    · have hbc : bc (g :: gs) = bc gs + 1 := by simp [bc, hb]
      rw [hbc]
      exact Or.inr ⟨a, b, ha, hb2, tail _ (ext _ (fun w hm => K_ins (hw w hm)) h)⟩

theorem bound_of_LB (F : BF n) (b : ℕ) (h : LB F b) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin n → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) : b ≤ bc gs := by
  apply h
  have hr := compile o gs (List.ofFn fun i : Fin n => fun x : Fin n → Bool => x i) (Vars n) hg (by
    intro w hw
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hw
    exact Or.inr (Or.inl ⟨i, rfl⟩))
  have e : (fun x : Fin n → Bool => (gs.foldl step ((List.ofFn fun i : Fin n =>
      fun x : Fin n → Bool => x i).map fun w => w x)).getD o false) = F := by
    funext x
    rw [← he x, List.map_ofFn]
    rfl
  rw [e] at hr
  exact hr

end Compile

section LiveProjection

variable {α ι : Type} [DecidableEq α]
variable {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}

private theorem lp_count_insert_le (C : α → Prop) [DecidablePred C] (w : α) (r : Finset α) :
    ((insert w r).filter C).card ≤ (r.filter C).card + (if C w then 1 else 0) := by
  by_cases h : C w
  · simpa [Finset.filter_insert, h] using Finset.card_insert_le w (r.filter C)
  · simp [Finset.filter_insert, h]

theorem live_project_steps (ev : α → ι → Bool) (C : α → Prop) [DecidablePred C]
    (h0 : ∀ w, C w → ∀ S, K S (ev w))
    (hboth : ∀ a b, ∀ z ∈ ops a b, C a → C b → C z)
    (hfree : ∀ a b, ∀ z ∈ ops a b, C a ∨ C b → ∀ S, K S (ev a) → K S (ev b) → K S (ev z))
    (hgate : ∀ a b, ∀ z ∈ ops a b, ∀ S, K S (ev a) → K S (ev b) →
      K S (ev z) ∨ ∃ u v, K S u ∧ K S v ∧ K (ins (fun i => u i && v i) S) (ev z))
    (hg : ¬ C goal) (h : live ops goal k s) (S : (ι → Bool) → Prop)
    (hs : ∀ w ∈ s, ¬ C w → K S (ev w)) :
    ∃ t, Run t S (ev goal) ∧ t + (s.filter C).card ≤ k := by
  induction k generalizing s S with
  | zero =>
    change s = {goal} at h
    subst s
    exact ⟨0, hs goal (by simp) hg, by simp [hg]⟩
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, _, z, hz, hout, r, hsr, tail⟩
    · obtain ⟨t, ht, hn⟩ := ih h S hs
      exact ⟨t, ht, by omega⟩
    · have knew : ∀ w ∈ s, K S (ev w) := by
        intro w hw
        by_cases hc : C w
        · exact h0 w hc S
        · exact hs w hw hc
      have ka := knew a ha
      have kb := knew b hb
      subst s
      have kr : ∀ w ∈ r, K S (ev w) := fun w hw => knew w (by simp [hw])
      have hzr : z ∉ r := fun hw => hout (by simp [hw])
      have cnt₁ := lp_count_insert_le C a (insert b r)
      have cnt₂ := lp_count_insert_le C b r
      have cnt₃ : ((insert z r).filter C).card =
          (r.filter C).card + (if C z then 1 else 0) := by
        by_cases hc : C z
        · simp [Finset.filter_insert, hc, Finset.card_insert_of_notMem, hzr]
        · simp [Finset.filter_insert, hc]
      have skip : K S (ev z) → ∃ t, Run t S (ev goal) ∧
          t + ((insert z r).filter C).card ≤ k := by
        intro kz
        apply ih tail S
        intro w hw _
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact kz
        · exact kr w hw
      by_cases cheap : C a ∨ C b
      · obtain ⟨t, ht, hcount⟩ := skip (hfree a b z hz cheap S ka kb)
        refine ⟨t, ht, ?_⟩
        have both := hboth a b z hz
        by_cases ca : C a <;> by_cases cb : C b <;> by_cases cz : C z <;>
          simp_all only [↓reduceIte, or_self, or_false, or_true] <;> omega
      · obtain ⟨ca, cb⟩ := not_or.mp cheap
        simp only [ca, cb, ite_false, Nat.add_zero] at cnt₁ cnt₂
        rcases hgate a b z hz S ka kb with kz | ⟨u, v, ku, kv, kz⟩
        · obtain ⟨t, ht, hn⟩ := skip kz
          exact ⟨t, ht, by omega⟩
        · obtain ⟨t, ht, hn⟩ := ih tail (ins (fun i => u i && v i) S) (by
            intro w hw _
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact kz
            · exact K_ins (kr w hw))
          exact ⟨t+1, Or.inr ⟨u, v, ku, kv, ht⟩, by omega⟩

private theorem lp_xor {S : (ι → Bool) → Prop} {w : ι → Bool}
    (p : Bool) (h : K S w) : K S (fun i => Bool.xor p (w i)) := by
  cases p
  · simpa using h
  · simpa using K_not h

theorem live_project_loss (ev : α → ι → Bool) (C : α → Prop) [DecidablePred C]
    (hc : ∀ w, C w ↔ ∃ c : Bool, ev w = fun _ => c)
    (hop : ∀ a b, ∀ z ∈ ops a b, ∃ pa pb pz : Bool, ∀ i,
      ev z i = Bool.xor pz (Bool.xor pa (ev a i) && Bool.xor pb (ev b i)))
    (hg : ¬ C goal) (h : live ops goal k s) (S : (ι → Bool) → Prop)
    (hs : ∀ w ∈ s, ¬ C w → K S (ev w)) :
    ∃ t, Run t S (ev goal) ∧ t + (s.filter C).card ≤ k := by
  apply live_project_steps ev C _ _ _ _ hg h S hs
  · intro w hw _
    exact Or.inl ((hc w).mp hw)
  · intro a b z hz ca cb
    obtain ⟨u, hu⟩ := (hc a).mp ca
    obtain ⟨v, hv⟩ := (hc b).mp cb
    obtain ⟨pa, pb, pz, hh⟩ := hop a b z hz
    exact (hc z).mpr ⟨_, funext fun i => by rw [hh, hu, hv]⟩
  · intro a b z hz cheap S ka kb
    obtain ⟨pa, pb, pz, hh⟩ := hop a b z hz
    rw [funext hh]
    apply lp_xor pz
    rcases cheap with ca | cb
    · obtain ⟨c, hc'⟩ := (hc a).mp ca
      exact K_and ⟨_, fun i => by rw [hc']⟩ (lp_xor pb kb)
    · obtain ⟨c, hc'⟩ := (hc b).mp cb
      simp_rw [Bool.and_comm (Bool.xor pa _) (Bool.xor pb _)]
      exact K_and ⟨_, fun i => by rw [hc']⟩ (lp_xor pa ka)
  · intro a b z hz S ka kb
    obtain ⟨pa, pb, pz, hh⟩ := hop a b z hz
    refine Or.inr ⟨_, _, lp_xor pa ka, lp_xor pb kb, ?_⟩
    rw [funext hh]
    exact lp_xor pz (K_new _)

end LiveProjection
section PoolPrune

abbrev R (d : ℕ) := {i : ℕ // d.testBit i = true}

def v (d w : ℕ) (i : R d) : Bool := w.testBit i.val

def PoolLB (d : ℕ) (roots : List ℕ) (g b : ℕ) : Prop :=
  ∀ k, Run k (fun w => ∃ a ∈ roots, w = v d a) (v d g) → b ≤ k

inductive HistOK (roots : List ℕ) : List ℕ → Prop
  | root : HistOK roots roots
  | cons {hist : List ℕ} {a b z : ℕ} : HistOK roots hist →
      a ∈ hist → b ∈ hist → z ∈ bops a b → HistOK roots (z :: hist)

def pconst (d w : ℕ) : Bool :=
  fz (Nat.land w d) fun t => t == 0 || t == d

def pcheap (d z : ℕ) (hist : List ℕ) : Bool :=
  fz (Nat.land z d) fun t => t == 0 || t == d ||
    fz (Nat.xor t d) fun n =>
      hist.any fun a => fz (Nat.land a d) fun u => u == t || u == n

def pcost (d : ℕ) : ℕ → List ℕ → ℕ
  | n + 1, z :: hist => if pcheap d z hist then pcost d n hist else (pcost d n hist).succ
  | _, _ => 0

def cost (d : ℕ) (roots hist : List ℕ) : ℕ :=
  pcost d (hist.length - roots.length) hist

def pprune (roots : List ℕ) (bounds : List (ℕ × ℕ)) (k : ℕ) (hist ws : List ℕ) : Bool :=
  bounds.any fun (d, b) => decide (k + cost d roots hist < b + ws.countP (pconst d))

private theorem pmask_bit (d w : ℕ) (i : R d) :
    (Nat.land w d).testBit i.val = v d w i := by
  simp [Nat.testBit_and, i.property, v]

theorem pconst_spec (d w : ℕ) : pconst d w = true ↔ ∃ c : Bool, v d w = fun _ => c := by
  simp only [pconst, fz_eq, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (h | h)
    · exact ⟨false, funext fun i => by rw [← pmask_bit, h]; simp⟩
    · exact ⟨true, funext fun i => by rw [← pmask_bit, h]; exact i.property⟩
  · rintro ⟨c, h⟩
    have hi (i : ℕ) (hd : d.testBit i = true) : w.testBit i = c :=
      congrFun h ⟨i, hd⟩
    cases c
    · left
      apply Nat.eq_of_testBit_eq
      intro i
      cases hd : d.testBit i <;> simp [Nat.testBit_and, hd, hi]
    · right
      apply Nat.eq_of_testBit_eq
      intro i
      cases hd : d.testBit i <;> simp [Nat.testBit_and, hd, hi]

theorem bops_signed (d a b z : ℕ) (hz : z ∈ bops a b) :
    ∃ pa pb pz : Bool, ∀ i, v d z i =
      Bool.xor pz (Bool.xor pa (v d a i) && Bool.xor pb (v d b i)) := by
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨false, false, false, fun i => by simp [v, Nat.testBit_and]⟩
  · refine ⟨true, true, true, fun i => ?_⟩
    simp only [v, Nat.testBit_or]
    cases a.testBit i.val <;> cases b.testBit i.val <;> rfl
  · refine ⟨false, true, false, fun i => ?_⟩
    simp only [v, Nat.testBit_xor, Nat.testBit_and]
    cases a.testBit i.val <;> cases b.testBit i.val <;> rfl
  · refine ⟨true, false, false, fun i => ?_⟩
    simp only [v, Nat.testBit_xor, Nat.testBit_and]
    cases a.testBit i.val <;> cases b.testBit i.val <;> rfl

private abbrev ppool (d : ℕ) (ws : List ℕ) : (R d → Bool) → Prop :=
  fun w => ∃ a ∈ ws, w = v d a

private theorem ppool_mem {d a : ℕ} {l : List ℕ} (ha : a ∈ l) : K (ppool d l) (v d a) :=
  Or.inr (Or.inl ⟨a, ha, rfl⟩)

private theorem pcheap_K {d z : ℕ} {hist : List ℕ} (h : pcheap d z hist = true) :
    K (ppool d hist) (v d z) := by
  simp only [pcheap, fz_eq, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
  rcases h with hc | ⟨a, ha, e | e⟩
  · apply Or.inl
    exact (pconst_spec d z).mp (by simpa [pconst, fz_eq] using hc)
  · have E : v d z = v d a := funext fun i => by rw [← pmask_bit, ← e, pmask_bit]
    exact E ▸ ppool_mem ha
  · have E : v d z = fun i => !v d a i := by
      funext i
      have he := congrArg (fun n : ℕ => n.testBit i.val) e
      change (Nat.land a d).testBit i.val = ((Nat.land z d) ^^^ d).testBit i.val at he
      simp only [Nat.testBit_xor, pmask_bit, i.property, Bool.xor_true] at he
      simp [he]
    rw [E]; exact K_not (ppool_mem ha)

private theorem ppool_remap {d z : ℕ} {l : List ℕ} {S : (R d → Bool) → Prop}
    (hz : K S (v d z)) (hl : ∀ a ∈ l, K S (v d a))
    {k : ℕ} {f : R d → Bool} (h : Run k (ppool d (z :: l)) f) : Run k S f := by
  apply Run_map id k (ppool d (z :: l)) S f _ h
  rintro _ ⟨a, ha, rfl⟩
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hz
  · exact hl _ ha

private theorem HistOK.plen {roots hist} (hh : HistOK roots hist) :
    roots.length ≤ hist.length := by
  induction hh with
  | root => rfl
  | cons _ _ _ _ ih => exact Nat.le.step ih

private theorem pcost_cons {d z : ℕ} {roots hist : List ℕ} (hh : HistOK roots hist) :
    cost d roots (z :: hist) =
      if pcheap d z hist then cost d roots hist else (cost d roots hist).succ := by
  have hlen := hh.plen
  have e : (z :: hist).length - roots.length = (hist.length - roots.length).succ := by
    simp only [List.length_cons]; omega
  simp only [cost, e, pcost]

theorem HistOK.cost_run {d : ℕ} {roots hist : List ℕ} (hh : HistOK roots hist)
    {f : R d → Bool} {k : ℕ} (h : Run k (ppool d hist) f) :
    Run (cost d roots hist + k) (ppool d roots) f := by
  induction hh generalizing k with
  | root => simpa [cost, pcost] using h
  | @cons hist a b z hh ha hb hz ih =>
    rw [pcost_cons hh]
    by_cases cheap : pcheap d z hist = true
    · simp only [cheap, ↓reduceIte]
      exact ih (ppool_remap (pcheap_K cheap) (fun _ ha => ppool_mem ha) h)
    · rw [ite_eq_right cheap, Nat.succ_add, ← Nat.add_succ]
      apply ih
      obtain ⟨pa, pb, pz, hbit⟩ := bops_signed d a b z hz
      refine Or.inr ⟨_, _, lp_xor pa (ppool_mem ha), lp_xor pb (ppool_mem hb), ?_⟩
      apply ppool_remap _ (fun _ hc => K_ins (ppool_mem hc)) h
      rw [funext hbit]
      exact lp_xor pz (K_new _)

theorem prune_ineq {d g b k : ℕ} {roots hist ws : List ℕ}
    (hg : pconst d g = false) (hb : PoolLB d roots g b) (hh : HistOK roots hist)
    (hn : ws.Nodup) (hw : ∀ w ∈ ws, w ∈ hist) (hl : live bops g k ws.toFinset) :
    b + ws.countP (pconst d) ≤ k + cost d roots hist := by
  obtain ⟨t, hr, hle⟩ := live_project_loss (v d) (fun w => pconst d w = true)
    (pconst_spec d) (bops_signed d) (by simp [hg]) hl (ppool d hist)
    (fun w hw' _ => ppool_mem (hw w (List.mem_toFinset.mp hw')))
  have lb := hb _ (hh.cost_run hr)
  rw [hn.card_eq_countP] at hle
  simpa using (show b + ws.countP (fun w => decide (pconst d w = true)) ≤ k + cost d roots hist by
    omega)

theorem pprune_sound {roots hist ws : List ℕ} {bounds : List (ℕ × ℕ)} {g k : ℕ}
    (hv : ∀ q ∈ bounds, pconst q.1 g = false ∧ PoolLB q.1 roots g q.2)
    (hh : HistOK roots hist) (hn : ws.Nodup) (hw : ∀ w ∈ ws, w ∈ hist)
    (hl : live bops g k ws.toFinset) : pprune roots bounds k hist ws = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  unfold pprune at h
  obtain ⟨⟨d,b⟩, hq, hc⟩ := List.any_eq_true.mp h
  obtain ⟨hg, hb⟩ := hv _ hq
  exact (Nat.not_lt_of_ge (prune_ineq hg hb hh hn hw hl)) (of_decide_eq_true hc)

end PoolPrune
namespace PSearchAux

def isOne (g : ℕ) : List ℕ → Bool
  | [w] => Nat.beq w g
  | _ => false

theorem isOne_self (g : ℕ) : isOne g [g] = true := Nat.beq_refl g

def memb (z : ℕ) : List ℕ → Bool
  | [] => false
  | w :: t => or (Nat.beq z w) (memb z t)

theorem memb_false {z : ℕ} : ∀ {ws : List ℕ}, z ∉ ws → memb z ws = false
  | [], _ => rfl
  | w :: t, h => by
    have h1 : z ≠ w := fun e => h (e ▸ List.mem_cons_self ..)
    have h2 : z ∉ t := fun e => h (List.mem_cons_of_mem _ e)
    show or (Nat.beq z w) (memb z t) = false
    rw [memb_false h2]
    cases hb : Nat.beq z w
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h1

def opsK (a b : ℕ) : List ℕ :=
  [Nat.land a b, Nat.lor a b, Nat.xor a (Nat.land a b), Nat.xor b (Nat.land a b)]

theorem opsK_eq (a b : ℕ) : opsK a b = ops a b := rfl

theorem all_false_of {α : Type} {l : List α} {p : α → Bool} {x : α} (hx : x ∈ l) (hp : p x = false) :
    l.all p = false := by
  cases h : l.all p
  · rfl
  · rw [List.all_eq_true] at h
    rw [h x hx] at hp
    exact absurd hp (by decide)

def kp (P m k : ℕ) (nx : List ℕ → Bool) (z : ℕ) (r : List ℕ) : Bool :=
  fzl r fun r => or (Nat.blt k r.length) (or (not (Nat.beq (cuts P m (z :: r)) m)) (nx (z :: r)))

def cand (P m k : ℕ) (nx : List ℕ → Bool) (ws : List ℕ) (cw : ℕ) (q : ℕ × ℕ × List ℕ) (z : ℕ) : Bool :=
  or (Nat.beq z 0) (or (memb z ws) (or (not (Nat.beq (Nat.lor (sep P m z) cw) m))
    ((keepChoices q.1 q.2.1 q.2.2).all fun r => kp P m k nx z r)))

theorem live_zero {g : ℕ} (hg : g ≠ 0) : ∀ {k : ℕ} {s : Finset ℕ}, live bops g k s → 0 ∉ s := by
  intro k
  induction k with
  | zero =>
    intro s h h0
    change s = {g} at h
    subst h
    exact hg (Finset.mem_singleton.mp h0).symm
  | succ k ih =>
    intro s h h0
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih h h0
    · have h1 := ih tail
      have hz0 : z ≠ 0 := fun e => h1 (e ▸ Finset.mem_insert_self _ _)
      have hr0 : 0 ∉ rest := fun e => h1 (Finset.mem_insert_of_mem e)
      rcases Finset.mem_insert.mp h0 with e | e
      · rw [← e] at hz
        rcases bops_zero hz with e2 | e2
        · exact hz0 e2
        · exact hout (by rw [e2]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      · rcases Finset.mem_insert.mp e with e | e
        · rw [← e, ops_swap] at hz
          rcases bops_zero hz with e2 | e2
          · exact hz0 e2
          · exact hout (by rw [e2]; exact Finset.mem_insert_self _ _)
        · exact hr0 e

theorem cuts_sup {P : ℕ} {ws ws' : List ℕ} (hsub : ∀ w ∈ ws, w ∈ ws')
    (h : cuts P (2 ^ P - 1) ws = 2 ^ P - 1) : cuts P (2 ^ P - 1) ws' = 2 ^ P - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [mask_bit]
  by_cases hi : i < P
  · have h1 : (cuts P (2 ^ P - 1) ws).testBit i = true := by rw [h, mask_bit]; simp [hi]
    obtain ⟨_, w, hw, hd⟩ := (cuts_spec P ws i).mp h1
    have := (cuts_spec P ws' i).mpr ⟨hi, w, hsub w hw, hd⟩
    simpa [hi] using this
  · cases hb : (cuts P (2 ^ P - 1) ws').testBit i
    · simp [hi]
    · exact absurd ((cuts_spec P ws' i).mp hb).1 hi

def stepP (P m g k : ℕ) (prune : ℕ → List ℕ → List ℕ → Bool)
    (nx : List ℕ → List ℕ → Bool) (hist ws : List ℕ) : Bool :=
  and (not (isOne g ws)) (or (prune k.succ hist ws) (fz (cuts P m ws) fun cw =>
    (pairs ws).all fun q => (opsK q.1 q.2.1).all fun z0 => fz z0 fun z =>
      cand P m k (nx (z :: hist)) ws cw q z))

end PSearchAux

open PSearchAux in
def psrch (P m g : ℕ) (prune : ℕ → List ℕ → List ℕ → Bool)
    (k : ℕ) (hist ws : List ℕ) : Bool :=
  Nat.rec (motive := fun _ => List ℕ → List ℕ → Bool) (fun _ ws => not (isOne g ws))
    (fun k ih hist ws => stepP P m g k prune ih hist ws) k hist ws

section PSearchSound
open PSearchAux

variable {P g : ℕ} {prune : ℕ → List ℕ → List ℕ → Bool} {ValidHist : List ℕ → Prop}
  (hg0 : g ≠ 0) (hg : ∀ i < P, differs P i g)
  (hcons : ∀ hist z, ValidHist hist → (∃ a ∈ hist, ∃ b ∈ hist, z ∈ bops a b) → ValidHist (z :: hist))
  (hp : ∀ k hist ws, ValidHist hist → ws.Nodup → ws.toFinset ⊆ hist.toFinset →
    live bops g k ws.toFinset → prune k hist ws = false)

include hg0 hg hcons hp

theorem psrch_sound : ∀ k hist (ws : List ℕ), ValidHist hist → ws.Nodup → ws.toFinset ⊆ hist.toFinset →
    live bops g k ws.toFinset → psrch P (2 ^ P - 1) g prune k hist ws = false := by
  intro k
  induction k with
  | zero =>
    intro hist ws hv hn hsub h
    rw [singleton_list hn h]
    show (not (isOne g [g])) = false
    rw [isOne_self]; rfl
  | succ k ih =>
    intro hist ws hv hn hsub h
    show stepP P (2 ^ P - 1) g k prune (psrch P (2 ^ P - 1) g prune k) hist ws = false
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, rest, hs, tail⟩
    · rw [singleton_list hn done]
      show and (not (isOne g [g])) _ = false
      rw [isOne_self]; rfl
    · have ha' : a ∈ ws := List.mem_toFinset.mp ha
      have hb' : b ∈ ws := List.mem_toFinset.mp hb
      obtain ⟨r, hm, hpr⟩ := pick_two ha' hb' hab
      have hz0 : z ≠ 0 := fun e => live_zero hg0 tail (e ▸ Finset.mem_insert_self _ _)
      have hzw : z ∉ ws := fun e => hout (List.mem_toFinset.mpr e)
      have hvalid : ValidHist (z :: hist) := hcons _ _ hv
        ⟨a, List.mem_toFinset.mp (hsub ha), b, List.mem_toFinset.mp (hsub hb), hz⟩
      have key : ∀ a b : ℕ, (a, b, r) ∈ pairs ws → ws.Perm (a :: b :: r) → z ∈ bops a b →
          ws.toFinset = insert a (insert b rest) →
          stepP P (2 ^ P - 1) g k prune (psrch P (2 ^ P - 1) g prune k) hist ws = false := by
        intro a b hmem hperm hzab hset
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept hperm hn hset
        have hkw : ∀ w ∈ kept, w ∈ ws := by
          intro w hw
          have h1 : w ∈ rest := hfin ▸ List.mem_toFinset.mpr hw
          have h2 : w ∈ ws.toFinset := by
            rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h1)
          exact List.mem_toFinset.mp h2
        have hzk : z ∉ kept := fun e => hzw (hkw z e)
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hzk, hnk⟩
        have hl : live bops g k (z :: kept).toFinset := by
          rw [List.toFinset_cons, hfin]; exact tail
        have hsub' : (z :: kept).toFinset ⊆ (z :: hist).toFinset := by
          simp only [List.toFinset_cons]
          exact Finset.insert_subset_insert _ (fun w hw => hsub (List.mem_toFinset.mpr
            (hkw w (List.mem_toFinset.mp hw))))
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have hcut := cuts_full hg hl
        have hcut2 : cuts P (2 ^ P - 1) (z :: ws) = 2 ^ P - 1 := by
          refine cuts_sup ?_ hcut
          intro w hw
          rcases List.mem_cons.mp hw with e | e
          · rw [e]; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (hkw w e)
        have hblt : Nat.blt k kept.length = false := by
          cases hq : Nat.blt k kept.length
          · rfl
          · have := Nat.blt_eq.mp hq; omega
        have hkp : kp P (2 ^ P - 1) k (psrch P (2 ^ P - 1) g prune k (z :: hist)) z kept = false := by
          unfold kp
          rw [fzl_eq, hblt, hcut, Nat.beq_refl, ih _ _ hvalid hnd hsub' hl]; rfl
        have hz0' : Nat.beq z 0 = false := by
          cases hq : Nat.beq z 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hq) hz0
        have hlor : Nat.lor (sep P (2 ^ P - 1) z) (cuts P (2 ^ P - 1) ws) = 2 ^ P - 1 := hcut2
        have hcand : cand P (2 ^ P - 1) k (psrch P (2 ^ P - 1) g prune k (z :: hist)) ws (cuts P (2 ^ P - 1) ws)
            (a, b, r) z = false := by
          unfold cand
          rw [hz0', memb_false hzw, hlor, Nat.beq_refl, all_false_of hk hkp]; rfl
        unfold stepP
        rw [hp _ _ _ hv hn hsub h, fz_eq]
        have hall : ((pairs ws).all fun q => (opsK q.1 q.2.1).all fun z0 => fz z0 fun z =>
            cand P (2 ^ P - 1) k (psrch P (2 ^ P - 1) g prune k (z :: hist)) ws (cuts P (2 ^ P - 1) ws) q z) = false := by
          refine all_false_of hmem ?_
          refine all_false_of (x := z) ?_ ?_
          · rw [opsK_eq]; exact List.mem_toFinset.mp hzab
          · rw [fz_eq]; exact hcand
        rw [hall]
        cases (not (isOne g ws)) <;> rfl
      rcases hm with hm | hm
      · exact key a b hm hpr hz hs
      · exact key b a hm (hpr.trans (List.Perm.swap b a r)) (ops_swap a b ▸ hz)
          (by rw [hs, Finset.insert_comm])

def ptop (P m g : ℕ) (prune : ℕ → List ℕ → List ℕ → Bool) (k : ℕ) (inp : List ℕ) : Bool :=
  inp.sublists.all fun ws =>
    or (Nat.blt k.succ ws.length)
      (or (not (Nat.beq (cuts P m ws) m)) (psrch P m g prune k inp ws))

theorem ptop_sound (k : ℕ) (inp : List ℕ) (hv : ValidHist inp) (hn : inp.Nodup)
    {s : Finset ℕ} (hs : s ⊆ inp.toFinset) (hl : live bops g k s) :
    ptop P (2 ^ P - 1) g prune k inp = false := by
  classical
  let ws := inp.filter (· ∈ s)
  have e : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hn' : ws.Nodup := hn.filter _
  have hl' : live bops g k ws.toFinset := e.symm ▸ hl
  have h := psrch_sound hg0 hg hcons hp k inp ws hv hn' (e.symm ▸ hs) hl'
  have hc := live_card hl'
  rw [List.toFinset_card_of_nodup hn'] at hc
  have hb : Nat.blt k.succ ws.length = false := by
    cases hq : Nat.blt k.succ ws.length
    · rfl
    · have := Nat.blt_eq.mp hq; omega
  unfold ptop
  apply all_false_of (x := ws) (List.mem_sublists.mpr (List.filter_sublist ..))
  rw [hb, cuts_full hg hl', Nat.beq_refl, h]; rfl

end PSearchSound
section PoolEntry


theorem pbase_build {n k t g : ℕ} (f : BF n) (roots : List ℕ)
    (x0 : Fin n → Bool) (pts : List (Fin n → Bool))
    (hroot : ∀ i : Fin n, code x0 pts (fun x => x i) ∈ roots)
    (hgcode : code x0 pts f = g) (hg0 : g ≠ 0)
    (htk : t ≤ k) (hr : Run t (Vars n) f) :
    build bops g k roots.toFinset := by
  rw [← hgcode]
  apply sim x0 pts f (hgcode.symm ▸ hg0) k (Vars n) roots.toFinset _ (Run_le htk hr)
  rintro w ⟨i, rfl⟩
  exact Or.inr (List.mem_toFinset.mpr (hroot i))



theorem pbase_of_check {n : ℕ} (f : BF n) (roots : List ℕ) (g k : ℕ)
    (x0 : Fin n → Bool) (pts : List (Fin n → Bool))
    (hroot : ∀ i : Fin n, code x0 pts (fun x => x i) ∈ roots)
    (hgcode : code x0 pts f = g) (hg0 : g ≠ 0)
    {check : Bool} (hsound : ∀ s ⊆ roots.toFinset, live bops g k s → check = false)
    (hcheck : check = true) : LB f (k + 1) := by
  intro t hr
  by_contra hlt
  have hbuild := pbase_build f roots x0 pts hroot hgcode hg0 (show t ≤ k by omega) hr
  obtain ⟨s, hs, hl⟩ := compress hbuild
  exact Bool.noConfusion (hcheck.symm.trans (hsound s hs hl))

end PoolEntry
theorem pbase {n : ℕ} (f : BF n) (roots : List ℕ) (g P k : ℕ)
    (x0 : Fin n → Bool) (pts : List (Fin n → Bool))
    (hroot : ∀ i : Fin n, code x0 pts (fun x => x i) ∈ roots)
    (hgcode : code x0 pts f = g) (hg0 : g ≠ 0)
    (hg : ∀ i < P, differs P i g)
    (prune : ℕ → List ℕ → List ℕ → Bool) (ValidHist : List ℕ → Prop)
    (hcons : ∀ hist z, ValidHist hist →
      (∃ a ∈ hist, ∃ b ∈ hist, z ∈ bops a b) → ValidHist (z :: hist))
    (hp : ∀ j hist ws, ValidHist hist → ws.Nodup → ws.toFinset ⊆ hist.toFinset →
      live bops g j ws.toFinset → prune j hist ws = false)
    (hv : ValidHist roots) (hn : roots.Nodup)
    (htop : ptop P (2 ^ P - 1) g prune k roots = true) : LB f (k + 1) := by
  refine pbase_of_check f roots g k x0 pts hroot hgcode hg0 ?_ htop
  intro s hs hl
  exact ptop_sound hg0 hg hcons hp k roots hv hn hs hl

theorem pbase' {n : ℕ} (f : BF n) (roots : List ℕ) (g P k : ℕ)
    (x0 : Fin n → Bool) (pts : List (Fin n → Bool))
    (hroot : ∀ i : Fin n, code x0 pts (fun x => x i) ∈ roots)
    (hgcode : code x0 pts f = g) (hg0 : g ≠ 0)
    (hg : ∀ i < P, differs P i g)
    (bounds : List (ℕ × ℕ))
    (hsoundProof : ∀ q ∈ bounds, pconst q.1 g = false ∧ PoolLB q.1 roots g q.2)
    (hn : roots.Nodup)
    (htop : ptop P (2 ^ P - 1) g (pprune roots bounds) k roots = true) : LB f (k + 1) := by
  refine pbase f roots g P k x0 pts hroot hgcode hg0 hg
    (pprune roots bounds) (HistOK roots) ?_ ?_ HistOK.root hn htop
  · rintro hist z hh ⟨a, ha, b, hb, hz⟩
    exact hh.cons ha hb hz
  · intro j hist ws hh hws hsub hl
    exact pprune_sound hsoundProof hh hws (fun w hw =>
      List.mem_toFinset.mp (hsub (List.mem_toFinset.mpr hw))) hl
def sampleIdx {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (List.ofFn x).foldr (fun b z => b.toNat + 2*z) 0

def tbl (n t : ℕ) : BF n := fun x => t.testBit (sampleIdx x)

def sLit (n j : ℕ) : BF n := fun x => if h : j<n then x ⟨j,h⟩ else decide (n<j)

theorem sLitK (n j : ℕ) : K (Vars n) (sLit n j) := by
  by_cases h : j<n
  · exact Or.inr (Or.inl ⟨⟨j,h⟩, funext fun x => by simp [sLit,h]⟩)
  · exact Or.inl ⟨decide (n<j), funext fun x => by simp [sLit,h]⟩

theorem poolFrom {n : ℕ} (f : BF n) {b : ℕ} (hf : LB f b) (d g : ℕ) (roots ls : List ℕ)
    (idx : (Fin n → Bool) → ℕ)
    (hd : ∀ x, d.testBit (idx x) = true)
    (hg : ∀ x, g.testBit (idx x) = f x)
    (hR : ∀ i : Fin roots.length, ∀ x, (roots.get i).testBit (idx x) = sLit n (ls.getD i.val n) x) :
    PoolLB d roots g b := by
  intro k h
  let pick : (Fin n → Bool) → R d := fun x => ⟨idx x, hd x⟩
  have hmap := Run_map pick k _ (Vars n) _ (by
    rintro w ⟨a, ha, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact (funext (hR i)).symm ▸ sLitK n (ls.getD i.val n)) h
  exact hf k ((funext hg) ▸ hmap)

def packedSample (n p neg pos : ℕ) : List (Fin n → Bool) :=
  (((List.range p).map (fun i => (neg >>> (n*i)) % 2^n)) ++
    ((List.range p).map (fun i => (pos >>> (n*i)) % 2^n)) ++ List.range (2^n)).map (pt n)

theorem pbits (g P i : ℕ) (hi : i < P) (h : g % 2^P = 0 ∧ (g >>> P) % 2^P = 2^P-1) :
    differs P i g := by
  have h0 := congrArg (fun w : ℕ => w.testBit i) h.1
  have h1 := congrArg (fun w : ℕ => w.testBit i) h.2
  simp [Nat.testBit_mod_two_pow, hi, Nat.testBit_two_pow_sub_one] at h0 h1
  simp [differs,h0,h1]

theorem finishPool {n : ℕ} (f : BF n) (roots : List ℕ) (g P k : ℕ)
    (pts : List (Fin n → Bool)) (bounds : List (ℕ × ℕ))
    (hroot : ∀ i : Fin n, code (pt n 0) pts (fun x => x i) ∈ roots)
    (hcode : code (pt n 0) pts f = g) (hg0 : g ≠ 0)
    (hg : ∀ i < P, differs P i g)
    (hv : ∀ q ∈ bounds, pconst q.1 g = false ∧ PoolLB q.1 roots g q.2)
    (hn : roots.Nodup)
    (h : ptop P (2^P-1) g (pprune roots bounds) k roots = true) : LB f (k+1) :=
  pbase f roots g P k (pt n 0) pts hroot hcode hg0 hg _ (HistOK roots)
    (by rintro hist z hH ⟨a,ha,b,hb,hz⟩; exact HistOK.cons hH ha hb hz)
    (by intro j hist ws hh hw hs hl
        exact pprune_sound hv hh hw (fun w h => List.mem_toFinset.mp (hs (List.mem_toFinset.mpr h))) hl)
    HistOK.root hn h

section SearchRows

open PSearchAux


private def withRowKeepCuts {β : Type} (P m a b : ℕ) (r : List ℕ)
    (f : List (List ℕ × ℕ × ℕ) → β) : β :=
  fz r.length fun n =>
  fz (cuts P m r) fun cr =>
  fz (sep P m a) fun ca =>
  fz (sep P m b) fun cb =>
  fz (Nat.lor ca cr) fun car =>
  fz (Nat.lor cb cr) fun cbr =>
  fz (Nat.lor ca cbr) fun cabr =>
  let br := b :: r
  f [(r, n, cr), (a :: r, n+1, car), (br, n+1, cbr), (a :: br, n+2, cabr)]

private theorem withRowKeepCuts_eq {β : Type} (P m a b : ℕ) (r : List ℕ)
    (f : List (List ℕ × ℕ × ℕ) → β) :
    withRowKeepCuts P m a b r f = f ((keepChoices a b r).map (fun l => (l, l.length, cuts P m l))) := by
  simp only [withRowKeepCuts, fz_eq]
  rfl

def rowKids (P m k : ℕ) (ws : List ℕ) (q : ℕ × ℕ × List ℕ) : List (List ℕ) :=
  let (a, b, r) := q
  withRowKeepCuts P m a b r fun ks =>
  (opsK a b).flatMap fun z =>
    fz z fun z =>
    if Nat.beq z 0 || memb z ws then [] else
      fz (sep P m z) fun cz =>
      ks.filterMap fun (kept, n, ck) =>
        if Nat.blt k n || !(Nat.beq (Nat.lor cz ck) m) then none else some (z :: kept)


theorem rowKids_spec (P m k : ℕ) (ws : List ℕ) (q : ℕ × ℕ × List ℕ) :
    rowKids P m k ws q =
      (opsK q.1 q.2.1).flatMap fun z =>
        if Nat.beq z 0 || memb z ws then [] else
          (keepChoices q.1 q.2.1 q.2.2).filterMap fun kept =>
            if Nat.blt k kept.length || !(Nat.beq (cuts P m (z :: kept)) m)
            then none else some (z :: kept) := by
  obtain ⟨a, b, r⟩ := q
  simp only [rowKids, fz_eq, withRowKeepCuts_eq, List.filterMap_map, Function.comp_apply]
  rfl

def nextKids (P m k : ℕ) (ws : List ℕ) :=
  (pairs ws).flatMap (rowKids P m k ws)

theorem psrch_of_next {P m g k : ℕ} {prune : ℕ → List ℕ → List ℕ → Bool}
    {hist ws : List ℕ} (ho : PSearchAux.isOne g ws = false)
    (hn : ∀ w ∈ nextKids P m k ws, psrch P m g prune k (w.headD 0 :: hist) w = true) :
    psrch P m g prune (k+1) hist ws = true := by
  change stepP P m g k prune (psrch P m g prune k) hist ws = true
  simp only [stepP, ho, Bool.not_false, Bool.true_and, fz_eq]
  apply Bool.or_eq_true_iff.mpr
  right
  apply List.all_eq_true.mpr
  intro q hq
  apply List.all_eq_true.mpr
  intro z hz
  simp only [cand, Bool.or_eq_true]
  by_cases hz0 : Nat.beq z 0 = true
  · exact Or.inl hz0
  right
  by_cases hzw : memb z ws = true
  · exact Or.inl hzw
  right
  right
  apply List.all_eq_true.mpr
  intro kept hk
  simp only [kp, fzl_eq, Bool.or_eq_true]
  by_cases hlen : Nat.blt k kept.length = true
  · exact Or.inl hlen
  right
  by_cases hcut : Nat.beq (cuts P m (z :: kept)) m = false
  · exact Or.inl (by rw [hcut]; rfl)
  right
  change psrch P m g prune k ((z :: kept).headD 0 :: hist) (z :: kept) = true
  apply hn
  apply List.mem_flatMap.mpr
  refine ⟨q, hq, ?_⟩
  rw [rowKids_spec]
  refine List.mem_flatMap.mpr ⟨z, hz, ?_⟩
  have hz0' : Nat.beq z 0 = false := Bool.eq_false_iff.mpr hz0
  have hzw' : memb z ws = false := Bool.eq_false_iff.mpr hzw
  simp only [hz0', hzw', Bool.false_or, Bool.false_eq_true, ite_false]
  refine List.mem_filterMap.mpr ⟨kept, hk, ?_⟩
  have hlen' : Nat.blt k kept.length = false := Bool.eq_false_iff.mpr hlen
  have hcut' : Nat.beq (cuts P m (z :: kept)) m = true := Bool.eq_true_of_ne_false hcut
  simp [hlen', hcut']

end SearchRows
section CertifiedHints

inductive PCert where
  | node (hints : ℕ) (children : List PCert)



def useBound (roots : List ℕ) (bounds : List (ℕ × ℕ)) (g k : ℕ)
    (hist ws : List ℕ) (idx : ℕ) : Bool :=
  match bounds[idx]? with
  | none => false
  | some (d,b) =>
    !(PSearchAux.isOne g ws) &&
      Nat.blt (k + cost d roots hist) (b + ws.countP (pconst d))

theorem useBound_sound {roots bounds g k hist ws idx}
    (h : useBound roots bounds g k hist ws idx = true) (P m : ℕ) :
    psrch P m g (pprune roots bounds) k hist ws = true := by
  unfold useBound at h
  split at h
  · contradiction
  next d b he =>
    obtain ⟨hn, hf⟩ := Bool.and_eq_true_iff.mp h
    have hp : pprune roots bounds k hist ws = true := by
      apply List.any_eq_true.mpr
      exact ⟨(d,b), List.mem_of_getElem? he, decide_eq_true (Nat.blt_eq.mp hf)⟩
    cases k with
    | zero => exact hn
    | succ k =>
      change (!PSearchAux.isOne g ws && (pprune roots bounds (k+1) hist ws || _)) = true
      rw [hn, hp]; rfl

def hintSeq {α : Type} (p : ℕ → List ℕ → Bool) (e : α → List ℕ → Bool)
    (h : ℕ) (cs : List α) (ws : List (List ℕ)) : Bool :=
  match ws with
  | [] => true
  | w :: ws => fz (h % 256) fun i =>
    if i = 0 then
      match cs with
      | [] => false
      | c :: rest => e c w && hintSeq p e (h >>> 8) rest ws
    else p (i-1) w && hintSeq p e (h >>> 8) cs ws

theorem hintSeq_sound {α : Type} {p} {e : α → List ℕ → Bool} {Q : List ℕ → Prop}
    (hp : ∀ i w, p i w = true → Q w) (he : ∀ c w, e c w = true → Q w) :
    ∀ {h cs ws}, hintSeq p e h cs ws = true → ∀ w ∈ ws, Q w := by
  intro h cs ws
  induction ws generalizing h cs with
  | nil => simp
  | cons w ws ih =>
    intro hc a ha
    rw [hintSeq.eq_def] at hc
    dsimp only at hc
    rw [fz_eq] at hc
    split at hc
    · cases cs with
      | nil => contradiction
      | cons c cs =>
        obtain ⟨ht, hs⟩ := Bool.and_eq_true_iff.mp hc
        rcases List.mem_cons.mp ha with rfl | ha
        · exact he _ _ ht
        · exact ih hs _ ha
    · obtain ⟨ht, hs⟩ := Bool.and_eq_true_iff.mp hc
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hp _ _ ht
      · exact ih hs _ ha

def certCheck (P m g : ℕ) (roots : List ℕ) (bounds : List (ℕ × ℕ)) :
    ℕ → List ℕ → List ℕ → PCert → Bool
  | 0, _, ws, _ => !(PSearchAux.isOne g ws)
  | k+1, hist, ws, .node h cs =>
    !(PSearchAux.isOne g ws) &&
      hintSeq (fun i w => useBound roots bounds g k (w.headD 0 :: hist) w i)
        (fun c w => certCheck P m g roots bounds k (w.headD 0 :: hist) w c)
        h cs (nextKids P m k ws)

theorem certCheck_sound (P m g : ℕ) (roots : List ℕ) (bounds : List (ℕ × ℕ)) :
    ∀ k hist ws c, certCheck P m g roots bounds k hist ws c = true →
      psrch P m g (pprune roots bounds) k hist ws = true := by
  intro k
  induction k with
  | zero => intro hist ws c h; exact h
  | succ k ih =>
    rintro hist ws ⟨h,cs⟩ hc
    obtain ⟨hn, hs⟩ := Bool.and_eq_true_iff.mp hc
    apply psrch_of_next (by simpa using hn)
    refine hintSeq_sound (Q := fun w => psrch P m g (pprune roots bounds) k (w.headD 0 :: hist) w = true)
      (p := fun i w => useBound roots bounds g k (w.headD 0 :: hist) w i)
      (e := fun c w => certCheck P m g roots bounds k (w.headD 0 :: hist) w c) ?_ ?_ hs
    · exact fun _ _ h => useBound_sound h P m
    · exact fun c w h => ih _ _ c h

def certRow (P m g : ℕ) (roots : List ℕ) (bounds : List (ℕ × ℕ))
    (k : ℕ) (hist ws : List ℕ) (q : ℕ × ℕ × List ℕ) : PCert → Bool
  | .node h cs =>
    hintSeq (fun i w => useBound roots bounds g k (w.headD 0 :: hist) w i)
      (fun c w => certCheck P m g roots bounds k (w.headD 0 :: hist) w c)
      h cs (rowKids P m k ws q)

theorem certRow_sound {P m g roots bounds k hist ws q c}
    (h : certRow P m g roots bounds k hist ws q c = true) :
    ∀ w ∈ rowKids P m k ws q,
      psrch P m g (pprune roots bounds) k (w.headD 0 :: hist) w = true := by
  cases c
  refine hintSeq_sound (Q := fun w => psrch P m g (pprune roots bounds) k (w.headD 0 :: hist) w = true)
    (p := fun i w => useBound roots bounds g k (w.headD 0 :: hist) w i)
    (e := fun c w => certCheck P m g roots bounds k (w.headD 0 :: hist) w c) ?_ ?_ h
  · exact fun _ _ hc => useBound_sound hc P m
  · exact fun c _ hc => certCheck_sound P m g roots bounds _ _ _ c hc

theorem psrch_of_rows {P m g roots bounds k hist ws}
    (hn : PSearchAux.isOne g ws = false)
    (h : ∀ q ∈ pairs ws, ∃ c, certRow P m g roots bounds k hist ws q c = true) :
    psrch P m g (pprune roots bounds) (k+1) hist ws = true := by
  apply psrch_of_next hn
  intro w hw
  obtain ⟨q,hq,hm⟩ := List.mem_flatMap.mp hw
  obtain ⟨c,hc⟩ := h q hq
  exact certRow_sound hc w hm

theorem ptop_at_root {P m g k prune roots}
    (hs : roots.sublists.all (fun ws : List ℕ =>
      ws == roots || Nat.blt k.succ ws.length || !(Nat.beq (cuts P m ws) m)) = true)
    (h : psrch P m g prune k roots roots = true) : ptop P m g prune k roots = true := by
  apply List.all_eq_true.mpr
  intro ws hm
  have h' := List.all_eq_true.mp hs ws hm
  simp only [Bool.or_eq_true, beq_iff_eq] at h'
  rcases h' with (rfl | h') | h'
  · simp [h]
  · simp [h']
  · simp [h']

end CertifiedHints


def embLit {m n : ℕ} (ls : List ℕ) (x : Fin m → Bool) (i : Fin n) :=
  sLit m (ls.getD i.val m) x

theorem pullLB {m n b : ℕ} (f : BF n) (g : BF m) (ls : List ℕ)
    (h : ∀ x, f (embLit ls x) = g x) (hg : LB g b) : LB f b := by
  intro t ht
  have hmap := Run_map (embLit ls) t (Vars n) (Vars m) f (by
    rintro w ⟨i, rfl⟩
    exact sLitK m _) ht
  exact hg t ((funext h) ▸ hmap)


def p6ws : List ℕ := [0xaab7b038, 0xccded1c0, 0xf0fb6e00]
def p6g : ℕ := 0xe8fff000
def p6pts := packedSample 3 12 0x922489200 0xfafcfd7ab
def p6ds : List (ℕ × ℕ) := []

theorem p6lb : LB (tbl 3 0xe8) 4 := by
  apply finishPool (tbl 3 0xe8) p6ws p6g 12 3 p6pts p6ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p6g % (2^12) = 0 ∧ (p6g >>> 12) % (2^12) = 2^12-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp [p6ds] at ht
  · decide +kernel
  · decide +kernel

def p5ws : List ℕ := [0xaaaa55557f2c0000fc0, 0xcccc9a6fd554003f000, 0xf0f0e3f9a6980fc0000, 0xff00ff8e38e3f000000]
def p5g : ℕ := 0xfee8fffffffc0000000
def p5pts := packedSample 4 30 0x888888444444222222111111000000 0xedcba9edc765eba763db9753ca9653
def p5ds : List (ℕ × ℕ) := [(0xff <<< 60, 4), (0xf0f <<< 60, 4), (0x3333 <<< 60, 4), (0x5555 <<< 60, 4)]
theorem p5c0 : PoolLB (0xff <<< 60) p5ws p5g 4 :=
  poolFrom (tbl 3 0xe8) p6lb _ _ _ [0, 1, 2, 3] (fun x => 60 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p5c1 : PoolLB (0xf0f <<< 60) p5ws p5g 4 :=
  poolFrom (tbl 3 0xe8) p6lb _ _ _ [0, 1, 3, 2] (fun x => 60 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p5c2 : PoolLB (0x3333 <<< 60) p5ws p5g 4 :=
  poolFrom (tbl 3 0xe8) p6lb _ _ _ [0, 3, 1, 2] (fun x => 60 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p5c3 : PoolLB (0x5555 <<< 60) p5ws p5g 4 :=
  poolFrom (tbl 3 0xe8) p6lb _ _ _ [3, 0, 1, 2] (fun x => 60 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def p5hints : PCert := .node 0x10200010103000102030002010400010204000203040003 [
  .node 0x3000300040004000304030303010000010200000203040303 [
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x20302 [
      .node 0x20203 []
    ],
    .node 0x10301 [
      .node 0x10103 []
    ],
    .node 0x20402 [
      .node 0x20203 []
    ],
    .node 0x10401 [
      .node 0x10103 []
    ]
  ],
  .node 0x2000200040004000204020202010000010300000302040202 [
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x30202 [
      .node 0x20302 []
    ],
    .node 0x10201 [
      .node 0x10102 []
    ],
    .node 0x30403 [
      .node 0x30202 []
    ],
    .node 0x10401 [
      .node 0x10102 []
    ]
  ],
  .node 0x1000100040004000104010101020000020300000301040101 [
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x30101 [
      .node 0x10301 []
    ],
    .node 0x20101 [
      .node 0x10201 []
    ],
    .node 0x30403 [
      .node 0x30101 []
    ],
    .node 0x20402 [
      .node 0x20101 []
    ]
  ],
  .node 0x2000200030003000203020202010000010400000402030202 [
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x40202 [
      .node 0x20302 []
    ],
    .node 0x10201 [
      .node 0x10102 []
    ],
    .node 0x40303 [
      .node 0x30202 []
    ],
    .node 0x10301 [
      .node 0x10102 []
    ]
  ],
  .node 0x1000100030003000103010101020000020400000401030101 [
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x40101 [
      .node 0x10301 []
    ],
    .node 0x20101 [
      .node 0x10201 []
    ],
    .node 0x40303 [
      .node 0x30101 []
    ],
    .node 0x20302 [
      .node 0x20101 []
    ]
  ],
  .node 0x1000100020002000102010101030000030400000401020101 [
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x40101 [
      .node 0x10201 []
    ],
    .node 0x30101 [
      .node 0x10201 []
    ],
    .node 0x40202 [
      .node 0x20101 []
    ],
    .node 0x30202 [
      .node 0x20101 []
    ]
  ]
]

theorem p5lb : LB (tbl 4 0xfee8) 7 := by
  apply finishPool (tbl 4 0xfee8) p5ws p5g 30 6 p5pts p5ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p5g % (2^30) = 0 ∧ (p5g >>> 30) % (2^30) = 2^30-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p5ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p5c0⟩
    · exact ⟨by decide +kernel, p5c1⟩
    · exact ⟨by decide +kernel, p5c2⟩
    · exact ⟨by decide +kernel, p5c3⟩
  · decide +kernel
  · apply ptop_at_root (by decide +kernel)
    apply certCheck_sound _ _ _ _ _ _ _ _ p5hints
    decide +kernel

def p4ws : List ℕ := [0x2aaaaaaa9262592a9192ff72bff26000000000001ff80ff80, 0x333333333b54924ddb24bbafe4a09ff80000ffc01ffff0000, 0x3c3c3c3c2388e471fdffd235293520000000ffffe00000000, 0x3fc03fc03c1f07ff1e4723c9d1c9c00003ff0000000000000, 0x3fffc0003fefff81e0783c0e1e0e1ffffc000000000000000]
def p4g : ℕ := 0x3ffebfa83fffffffffffffffffffe00000000000000000000
def p4pts := packedSample 5 81 0x1294a5294a529421084210841084210842108318c6318c631884210842108318c6318c63188421084208421084210800000000 0x1edeb17b527157359c5ab49c79ace1cd62d49f5ed47b98a39796ad1cd61cbbbce2f5a9272ead372d47cd6716ad272e29162925
def p4ds : List (ℕ × ℕ) := [(0x33333333 <<< 162, 7)]
theorem p4c0 : PoolLB (0x33333333 <<< 162) p4ws p4g 7 :=
  poolFrom (tbl 4 0xfee8) p5lb _ _ _ [0, 4, 1, 2, 3] (fun x => 162 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem p4lb : LB (tbl 5 0xfffafea0) 8 := by
  apply finishPool (tbl 5 0xfffafea0) p4ws p4g 81 7 p4pts p4ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p4g % (2^81) = 0 ∧ (p4g >>> 81) % (2^81) = 2^81-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p4ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl
    · exact ⟨by decide +kernel, p4c0⟩
  · decide +kernel
  · decide +kernel

theorem p3lb : LB (tbl 6 0xffffffeefffaee00) 9 := 
  rule1 (tbl 6 0xffffffeefffaee00) 1 false 8 8 0 9 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 6 0xffffffeefffaee00) 1 false) (tbl 5 0xfffafea0) [0, 5, 1, 2, 3, 4] (by decide +kernel) p4lb)

def p9ws : List ℕ := [0xaaaa555daaf94003f83e0, 0xcccc9a6edf528003ffc00, 0xf0f0e3f8f39cc0fc00000, 0xff00ff8f1ce73f0000000]
def p9g : ℕ := 0xfee0ffffffffc00000000
def p9pts := packedSample 4 34 0x8888884444443333333222221111100000 0xedcba9edc765fba9765eba76db975ca965
def p9ds : List (ℕ × ℕ) := [(0x3333 <<< 68, 4)]
theorem p9c0 : PoolLB (0x3333 <<< 68) p9ws p9g 4 :=
  poolFrom (tbl 3 0xe8) p6lb _ _ _ [0, 3, 1, 2] (fun x => 68 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem p9lb : LB (tbl 4 0xfee0) 5 := by
  apply finishPool (tbl 4 0xfee0) p9ws p9g 34 4 p9pts p9ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p9g % (2^34) = 0 ∧ (p9g >>> 34) % (2^34) = 2^34-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p9ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl
    · exact ⟨by decide +kernel, p9c0⟩
  · decide +kernel
  · decide +kernel

def p10ws : List ℕ := [0xaaaa5635eebf300007e1f0, 0xcccc9b6975ea403f07fe00, 0xf0f0e3bfc733903ff80000, 0xff00ffce79dcefc0000000]
def p10g : ℕ := 0xfea0fffffffff000000000
def p10pts := packedSample 4 36 0x888888666666444443333332222111110000 0xedcba9feca75edc75fba975eba7db975ca95
def p10ds : List (ℕ × ℕ) := [(0x3333 <<< 72, 4)]
theorem p10c0 : PoolLB (0x3333 <<< 72) p10ws p10g 4 :=
  poolFrom (tbl 3 0xe8) p6lb _ _ _ [0, 3, 1, 2] (fun x => 72 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem p10lb : LB (tbl 4 0xfea0) 5 := by
  apply finishPool (tbl 4 0xfea0) p10ws p10g 36 4 p10pts p10ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p10g % (2^36) = 0 ∧ (p10g >>> 36) % (2^36) = 2^36-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p10ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl
    · exact ⟨by decide +kernel, p10c0⟩
  · decide +kernel
  · decide +kernel

theorem p11lb : LB (tbl 4 0xfea8) 5 := 
  pullLB (tbl 4 0xfea8) (tbl 4 0xfee0) [2, 0, 1, 3] (by decide +kernel) p9lb

theorem p12lb : LB (tbl 4 0xfe88) 5 := 
  pullLB (tbl 4 0xfe88) (tbl 4 0xfea0) [0, 2, 1, 3] (by decide +kernel) p10lb

def p8ws : List ℕ := [0x2aaaaaaa89545a8b13937be937fc68000000000007ff00ff80, 0x33333333126865dea525bdb7f9289000003ff00007ffff0000, 0x3c3c3c3c238ef70cc67fd13a5a4d1801ffc0000ff800000000, 0x3fc03fc03c0f79ef7fc621c464722001fffffff00000000000, 0x3fffc0003fff81f078783e078783c7fe000000000000000000]
def p8g : ℕ := 0x3fffbab83ffffffffffffffffffff800000000000000000000
def p8pts := packedSample 5 83 0x4210842108420c6318c6318c6314a5294a5294a4210842108210842108420c6318c6318c63108421084208421084210800000000 0x7359c5ab49ca3eef3147b9a9317dbd624f72d26e6b3873569e5ab4734e62eef3945eb49cc5d5a7272ce6cd6716ad272e2928a4c5
def p8ds : List (ℕ × ℕ) := [(0xff00ff <<< 166, 5), (0xf0f0f0f <<< 166, 5), (0x33333333 <<< 166, 5), (0x55555555 <<< 166, 5)]
theorem p8c0 : PoolLB (0xff00ff <<< 166) p8ws p8g 5 :=
  poolFrom (tbl 4 0xfee0) p9lb _ _ _ [0, 1, 2, 4, 3] (fun x => 166 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p8c1 : PoolLB (0xf0f0f0f <<< 166) p8ws p8g 5 :=
  poolFrom (tbl 4 0xfea0) p10lb _ _ _ [0, 1, 4, 2, 3] (fun x => 166 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p8c2 : PoolLB (0x33333333 <<< 166) p8ws p8g 5 :=
  poolFrom (tbl 4 0xfea8) p11lb _ _ _ [0, 4, 1, 2, 3] (fun x => 166 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p8c3 : PoolLB (0x55555555 <<< 166) p8ws p8g 5 :=
  poolFrom (tbl 4 0xfe88) p12lb _ _ _ [4, 0, 1, 2, 3] (fun x => 166 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem p8lb : LB (tbl 5 0xfffeeae0) 7 := by
  apply finishPool (tbl 5 0xfffeeae0) p8ws p8g 83 6 p8pts p8ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p8g % (2^83) = 0 ∧ (p8g >>> 83) % (2^83) = 2^83-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p8ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p8c0⟩
    · exact ⟨by decide +kernel, p8c1⟩
    · exact ⟨by decide +kernel, p8c2⟩
    · exact ⟨by decide +kernel, p8c3⟩
  · decide +kernel
  · decide +kernel

def p14ws : List ℕ := [0xaaaa54a7e950003f80, 0xcccc99f54a901fc000, 0xf0f0e33a74e0000000, 0xff00fdc3870fe00000]
def p14g : ℕ := 0xfef8fffffff0000000
def p14pts := packedSample 4 28 0x8888888222222211111110000000 0xedcba94eba7643db97543ca96543
def p14ds : List (ℕ × ℕ) := [(0xf0f <<< 56, 4)]
theorem p14c0 : PoolLB (0xf0f <<< 56) p14ws p14g 4 :=
  poolFrom (tbl 3 0xe8) p6lb _ _ _ [0, 1, 3, 2] (fun x => 56 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem p14lb : LB (tbl 4 0xfef8) 5 := by
  apply finishPool (tbl 4 0xfef8) p14ws p14g 28 4 p14pts p14ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p14g % (2^28) = 0 ∧ (p14g >>> 28) % (2^28) = 2^28-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p14ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl
    · exact ⟨by decide +kernel, p14c0⟩
  · decide +kernel
  · decide +kernel

theorem p13lb : LB (tbl 5 0xfffaeea0) 7 := 
  rule2 (tbl 5 0xfffaeea0) 1 5 8 0 5 0 5 (by decide +kernel) (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 5 0xfffaeea0) 1 false) (tbl 4 0xfea8) [0, 4, 1, 2, 3] (by decide +kernel) p11lb) (pullLB (rs (tbl 5 0xfffaeea0) 1 true) (tbl 4 0xfef8) [0, 5, 1, 2, 3] (by decide +kernel) p14lb)

theorem p15lb : LB (tbl 5 0xfffaeca0) 7 := 
  rule2 (tbl 5 0xfffaeca0) 1 5 8 0 5 0 5 (by decide +kernel) (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 5 0xfffaeca0) 1 false) (tbl 4 0xfe88) [0, 4, 1, 2, 3] (by decide +kernel) p12lb) (pullLB (rs (tbl 5 0xfffaeca0) 1 true) (tbl 4 0xfef8) [0, 5, 1, 2, 3] (by decide +kernel) p14lb)

theorem p17lb : LB (tbl 4 0xfae0) 5 := 
  pullLB (tbl 4 0xfae0) (tbl 4 0xfea0) [0, 1, 3, 2] (by decide +kernel) p10lb

theorem p16lb : LB (tbl 5 0xffeefa00) 6 := 
  rule1 (tbl 5 0xffeefa00) 1 false 5 16 0 9 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 5 0xffeefa00) 1 false) (tbl 4 0xfae0) [0, 4, 1, 2, 3] (by decide +kernel) p17lb)

theorem p18lb : LB (tbl 5 0xfffeffe0) 6 := 
  rule1 (tbl 5 0xfffeffe0) 0 false 5 4 0 6 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 5 0xfffeffe0) 0 false) (tbl 4 0xfef8) [4, 0, 1, 2, 3] (by decide +kernel) p14lb)

def p7ws : List ℕ := [0x2aaaaaaaaaaaaaaa8895089a42aa429845644a88b7bdd9127fbc49f7f4457ff8a80000000000000000000000007fff000fff801fff800fff00, 0x3333333333333333111a112c84c5efd48a488d115bdeeffb911092fbbbff88911000000000003fff80000000007ffffff000001ffffff00000, 0x3c3c3c3c3c3c3c3c3ddca231071084e1139efe2263ef77bf7bdbff21208a112047fff000000000000003fff0007fffffffffffe00000000000, 0x3fc03fc03fc03fc021e043c1efe707061c1feffffd087a23a21d23423d13a23a180000003fffc0000003ffffff800000000000000000000000, 0x3fffc0003fffc0003e00fc01f7f9f7fbfff0f043820f843c43e23c83c21c43c4600000003ffffffffffc000000000000000000000000000000, 0x3fffffffc00000003fff7ffff801f803e01f007c03f007c07c03c0fc03e07c0787ffffffc00000000000000000000000000000000000000000]
def p7g : ℕ := 0x3ffffffbbfbebb803ffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000
def p7pts := packedSample 6 195 0x2492492492492492492492482082082082082082082061861861861861861861861849249249249249249249249041041041041041041030c30c30c30c30c30c30c2082082082082082082071c71c71c71c71c71c71c71861861861861861861451451451451451451441041041041041030c30c30c30c30c30c30c2082082082082082041041041041041041000000000000 0x3cdb5d30badb289e6962854e34cb1c2caa9a269638a1f3ae78c2879d71b699511289eb6cf2c2279b6975944d12b8d32c7071a6565544d1f2eb6ca1e75c50f38d289e2caa9a1c69938d2ca277be79a58df5d65533ce34bdae9e689e5d650f38ad6d9e585d5d55113cd274b2695c59550e373ae78e285b5d344f2ca272aa68e26964ce2cac6996385955344d2c9c288a1511289
def p7ds : List (ℕ × ℕ) := [(0xf0f0f0f0f0f0f0f <<< 390, 7), (0x3333333333333333 <<< 390, 7), (0x5555555555555555 <<< 390, 7), (0xff00ff00ff00ff <<< 390, 6), (0xf0f0f0f0f0f0f0f0 <<< 390, 6), (0xf0f00000f0f <<< 390, 5), (0xf000f000f000f <<< 390, 5), (0xf0f00000f0f0 <<< 390, 5)]
theorem p7c0 : PoolLB (0xf0f0f0f0f0f0f0f <<< 390) p7ws p7g 7 :=
  poolFrom (tbl 5 0xfffeeae0) p8lb _ _ _ [0, 1, 5, 2, 3, 4] (fun x => 390 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p7c1 : PoolLB (0x3333333333333333 <<< 390) p7ws p7g 7 :=
  poolFrom (tbl 5 0xfffaeea0) p13lb _ _ _ [0, 5, 1, 2, 3, 4] (fun x => 390 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p7c2 : PoolLB (0x5555555555555555 <<< 390) p7ws p7g 7 :=
  poolFrom (tbl 5 0xfffaeca0) p15lb _ _ _ [5, 0, 1, 2, 3, 4] (fun x => 390 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p7c3 : PoolLB (0xff00ff00ff00ff <<< 390) p7ws p7g 6 :=
  poolFrom (tbl 5 0xffeefa00) p16lb _ _ _ [0, 1, 2, 5, 3, 4] (fun x => 390 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p7c4 : PoolLB (0xf0f0f0f0f0f0f0f0 <<< 390) p7ws p7g 6 :=
  poolFrom (tbl 5 0xfffeffe0) p18lb _ _ _ [0, 1, 6, 2, 3, 4] (fun x => 394 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p7c5 : PoolLB (0xf0f00000f0f <<< 390) p7ws p7g 5 :=
  poolFrom (tbl 4 0xfee0) p9lb _ _ _ [0, 1, 4, 2, 4, 3] (fun x => 390 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p7c6 : PoolLB (0xf000f000f000f <<< 390) p7ws p7g 5 :=
  poolFrom (tbl 4 0xfea0) p10lb _ _ _ [0, 1, 4, 4, 2, 3] (fun x => 390 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 16 + (x 3).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p7c7 : PoolLB (0xf0f00000f0f0 <<< 390) p7ws p7g 5 :=
  poolFrom (tbl 4 0xfee0) p9lb _ _ _ [0, 1, 5, 2, 4, 3] (fun x => 394 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def p7hints : PCert := .node 0x6000600040004060400040101010100010100010101010101010102020202020202020202020201010101030303030303030303030303010101010301020202020302 [
  .node 0x4000402020202020202020303030303030303020202020302060606060406060402020202030303030505050500050405050402020202030303030303010101 [
    .node 0x20303030606030301010505 [],
    .node 0x2 [
      .node 0x0 []
    ],
    .node 0x500 [
      .node 0x0 []
    ]
  ],
  .node 0x6040804020202020202020203030303030303030202020203020608080808060400000402020202030303030505050505060405050402020202030303030303010101 [
    .node 0x40002 [
      .node 0x0 []
    ],
    .node 0x7 []
  ],
  .node 0x108010302030600010601010102020303040001010202030306040404000000000101080801010101020202020303030304040406 [
    .node 0x108020003000406 [
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 [],
        .node 0x0 []
      ]
    ],
    .node 0x80100020003 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x801 [],
    .node 0x108 [],
    .node 0x1000206 [
      .node 0x0 [
        .node 0x0 [],
        .node 0x0 []
      ]
    ],
    .node 0x80104 []
  ],
  .node 0x10103020301000202030304000202030300040404060000060101010102020000020202020303030304040400 [
    .node 0x1 [],
    .node 0x1010301000303 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x2 [],
    .node 0x80100020003 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x108 [],
    .node 0x1 [],
    .node 0x2010006 [
      .node 0x0 [
        .node 0x0 [],
        .node 0x0 []
      ]
    ],
    .node 0x204 [
      .node 0x0 []
    ],
    .node 0x2 [
      .node 0x0 []
    ]
  ],
  .node 0x10103020301000202030304040004060000060101010101000001020202020303030304040400 [
    .node 0x1 [],
    .node 0x203050603030101 [],
    .node 0x1 [],
    .node 0x801 [],
    .node 0x108 [],
    .node 0x1 [],
    .node 0x7 [],
    .node 0x500 [
      .node 0x0 []
    ]
  ],
  .node 0x103020301010108080303060006010202030300060606040000040101080801010101020202020303030306060600 [
    .node 0x801 [],
    .node 0x80100020003 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x801 [],
    .node 0x80104 []
  ],
  .node 0x103020301010108080303060106060006040000040101010101080801020202020303030306060600 [
    .node 0x801 [],
    .node 0x2 [
      .node 0x0 []
    ],
    .node 0x108 [],
    .node 0x801 []
  ]
]

theorem p7lb : LB (tbl 6 0xffffffeefefaee00) 9 := by
  apply finishPool (tbl 6 0xffffffeefefaee00) p7ws p7g 195 8 p7pts p7ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p7g % (2^195) = 0 ∧ (p7g >>> 195) % (2^195) = 2^195-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p7ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p7c0⟩
    · exact ⟨by decide +kernel, p7c1⟩
    · exact ⟨by decide +kernel, p7c2⟩
    · exact ⟨by decide +kernel, p7c3⟩
    · exact ⟨by decide +kernel, p7c4⟩
    · exact ⟨by decide +kernel, p7c5⟩
    · exact ⟨by decide +kernel, p7c6⟩
    · exact ⟨by decide +kernel, p7c7⟩
  · decide +kernel
  · apply ptop_at_root (by decide +kernel)
    apply certCheck_sound _ _ _ _ _ _ _ _ p7hints
    decide +kernel

def p20ws : List ℕ := [0xaaaaaaaa25515935139392fff17000000000000003ff00, 0xcccccccc49a1a25bbea57fc952900000003ff807fc0000, 0xf0f0f0f08e3bcc63db7fa492642003ff803ffff8000000, 0xff00ff00f03df7fe1c46472388c003ffffc00000000000, 0xffff0000fffe0783e078783c0f0ffc0000000000000000]
def p20g : ℕ := 0xfffeeea8fffffffffffffffffff0000000000000000000
def p20pts := packedSample 5 76 0x84210842108418c6318c6318c6210842108420c6318c6318c6310842108420842108421082108421084210000000000 0xe6b38b5693947dde628f735492f359c39ab527d7b524f728e51f2d5a39a72ead39396a38f359c5ab49ca3c5251524a3
def p20ds : List (ℕ × ℕ) := [(0xf0f0f0f <<< 152, 7)]
theorem p20c0 : PoolLB (0xf0f0f0f <<< 152) p20ws p20g 7 :=
  poolFrom (tbl 4 0xfee8) p5lb _ _ _ [0, 1, 4, 2, 3] (fun x => 152 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem p20lb : LB (tbl 5 0xfffeeea8) 8 := by
  apply finishPool (tbl 5 0xfffeeea8) p20ws p20g 76 7 p20pts p20ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p20g % (2^76) = 0 ∧ (p20g >>> 76) % (2^76) = 2^76-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p20ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl
    · exact ⟨by decide +kernel, p20c0⟩
  · decide +kernel
  · decide +kernel

theorem p19lb : LB (tbl 6 0xfffffffefefaeee0) 9 := 
  rule1 (tbl 6 0xfffffffefefaeee0) 1 false 8 4 0 5 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 6 0xfffffffefefaeee0) 1 false) (tbl 5 0xfffeeea8) [0, 5, 1, 2, 3, 4] (by decide +kernel) p20lb)

theorem p21lb : LB (tbl 6 0xfffffffafefeaaa0) 9 := 
  pullLB (tbl 6 0xfffffffafefeaaa0) (tbl 6 0xffffffeefffaee00) [3, 2, 0, 1, 4, 5] (by decide +kernel) p3lb

theorem p22lb : LB (tbl 6 0xfffffffafefcaaa0) 9 := 
  pullLB (tbl 6 0xfffffffafefcaaa0) (tbl 6 0xffffffeefefaee00) [3, 2, 0, 1, 4, 5] (by decide +kernel) p7lb

theorem p23lb : LB (tbl 5 0xfffeeca8) 7 := 
  pullLB (tbl 5 0xfffeeca8) (tbl 5 0xfffeeae0) [2, 0, 1, 3, 4] (by decide +kernel) p8lb

theorem p25lb : LB (tbl 5 0xfefeaaa0) 6 := 
  pullLB (tbl 5 0xfefeaaa0) (tbl 5 0xffeefa00) [3, 1, 0, 2, 4] (by decide +kernel) p16lb

theorem p24lb : LB (tbl 6 0xfffefffaeeeeee00) 7 := 
  rule1 (tbl 6 0xfffefffaeeeeee00) 1 false 6 8 0 9 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 6 0xfffefffaeeeeee00) 1 false) (tbl 5 0xfefeaaa0) [0, 5, 1, 2, 3, 4] (by decide +kernel) p25lb)

theorem p27lb : LB (tbl 5 0xfffeffa8) 6 := 
  pullLB (tbl 5 0xfffeffa8) (tbl 5 0xfffeffe0) [2, 0, 1, 3, 4] (by decide +kernel) p18lb

theorem p26lb : LB (tbl 6 0xfffffffeffffeee0) 7 := 
  rule1 (tbl 6 0xfffffffeffffeee0) 0 false 6 4 0 6 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 6 0xfffffffeffffeee0) 0 false) (tbl 5 0xfffeffa8) [5, 0, 1, 2, 3, 4] (by decide +kernel) p27lb)

theorem p28lb : LB (tbl 5 0xfffaee00) 6 := 
  pullLB (tbl 5 0xfffaee00) (tbl 5 0xffeefa00) [0, 1, 2, 4, 3] (by decide +kernel) p16lb

theorem p30lb : LB (tbl 4 0xeea8) 5 := 
  pullLB (tbl 4 0xeea8) (tbl 4 0xfea0) [3, 0, 1, 2] (by decide +kernel) p10lb

theorem p29lb : LB (tbl 5 0xfefaeee0) 6 := 
  rule1 (tbl 5 0xfefaeee0) 1 false 5 4 0 5 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 5 0xfefaeee0) 1 false) (tbl 4 0xeea8) [0, 4, 1, 2, 3] (by decide +kernel) p30lb)

theorem p31lb : LB (tbl 5 0xfffeeee0) 6 := 
  rule1 (tbl 5 0xfffeeee0) 0 false 5 4 0 6 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 5 0xfffeeee0) 0 false) (tbl 4 0xfea8) [4, 0, 1, 2, 3] (by decide +kernel) p11lb)

def p2ws : List ℕ := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa108950422688254a209260424b208554411aa211a842b4421a8425befbdd88449ffbfc225fbfee8424bffff0950000000000000000000000000000000000000000000000000000001fffff80001ffffc000fffff80003ffff000, 0xcccccccccccccccccccccccccccccccc2111a0844b104985f7fb5884924106a8822d4422d08558842d084adf7deeffefe2109044afdef77fffc211210a0000000000000001fffff8000000000000000000000000000000001fffffffffe00000000fffffffffc0000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fbddc9088c208e10412381091cf7df3d04301f7fe10863ef7e10831fbef77dfedf7ddbfff10444084904224020fffff800000000000000000000fffffc00001ffff80003ffff80001ffffffffffffffffff00000000000000000, 0xff00ff00ff00ff00ff00ff00ff00ff00421e0210f040f020823c0a11e0fbefcfeffe6843021183ffbfffffe410879088e4211c883208879091c844724300000000000000000000000000ffffffffffe000000003ffffffffe00000000000000000000000000000000000, 0xffff0000ffff0000ffff0000ffff000083e0041f007dffc703c0141e00fdf7f3f7bf9ffbfffffd0830210c0820f8210f0841e110c410f8211e1087840c00000000007ffffe0000000000fffffffffffffffffffc00000000000000000000000000000000000000000000, 0xffffffff00000000ffffffff00000000fc000fe0007efff9fbffe7ffff81f80207c0107c041e020fc041f0103f0041f0107e021f081f0041e020f8087000000000007fffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffff0000000000000000fffff7ffffff0001fc0007e000fe0003f8001f8007e003f0007e001fc0007e001f8003e00fe0007e003f000f80ffffffffff80000000000000000000000000000000000000000000000000000000000000000000000000000000]
def p2g : ℕ := 0xffffffffffffffeefffefffaeeeeee00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def p2pts := packedSample 7 360 0x891224489122448912244891224489122448902040810204081020408102040810204080c183060c183060c183060c183060c183060c182244891224489122448912244891224489122448102040810204081020408102040810203870e1c3870e1c3870e1c3870e1c3870e1c3870c183060c183060c183060c183060c183060c142850a142850a142850a142850a142840810204081020408102040810204060c183060c183060c183060c183060c182040810204081020408102040810204070e1c3870e1c3870e1c3870e1c3870e1c3870e183060c183060c183060c183060c183050a142850a142850a142850a142850a14204081020408102040810204060c183060c183060c183060c183060c183060810204081020408102040810204080810204081020408102040810204081000000000000000000000 0xe9b3365c982e56ab5284e9b324478d1614149c3464c587058a94a8d0992a4c88d161c283e3a72e3c305078e9cb86cd5a3364c542442488f2d59b1e2c109d3666c972b54a13a6488d09215c3464c58703868c98ac54a54264a911a1f97aedcb15263e7af1c34587cf1d3464b151c37c5cb566c5090f1d3970a0f1d3668c9222284f4b95aad4a0f1b356890f1d2e58a9223c2c54a54683868c989a3258a93244765c9d3664878b96ac5090f1d1e3868a13a2c4c952643858a94a8346470d16284e7af3e3c68b0dbaf4e992a33e5cb15263c70d179ab4e8f1a1365c9d3243c5cb121e38565ab363c582d56a74a9109d2e5488f1a27254991a2b458992a42c5470dc74e5c7870a0b3569d1a1365c992223c58a138a94a8d0e132549919a2c4c90e162b0d193161c162a52a34264a932234589c14244282a12212444509
def p2ds : List (ℕ × ℕ) := [(0xffff0000ffff0000ffff0000ffff <<< 720, 9), (0xff00ff00ff00ff00ff00ff00ff00ff <<< 720, 9), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f <<< 720, 9), (0x33333333333333333333333333333333 <<< 720, 9), (0x55555555555555555555555555555555 <<< 720, 9), (0xf000f000f000f000f000f000f000f <<< 720, 7), (0x5050505050505050505050505050505 <<< 720, 7), (0xffffffffffffffff <<< 720, 7), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 <<< 720, 7), (0xffff0000ffff <<< 720, 6), (0xf0f0f0f0f0f0f0f <<< 720, 6), (0xf0f0f0f000000000f0f0f0f <<< 720, 6), (0xf0f0f0f000000000f0f0f0f0 <<< 720, 6), (0xf000f00000000000f000f <<< 720, 5), (0x50505050000000005050505 <<< 720, 5)]
theorem p2c0 : PoolLB (0xffff0000ffff0000ffff0000ffff <<< 720) p2ws p2g 9 :=
  poolFrom (tbl 6 0xffffffeefffaee00) p3lb _ _ _ [0, 1, 2, 3, 6, 4, 5] (fun x => 720 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c1 : PoolLB (0xff00ff00ff00ff00ff00ff00ff00ff <<< 720) p2ws p2g 9 :=
  poolFrom (tbl 6 0xffffffeefefaee00) p7lb _ _ _ [0, 1, 2, 6, 3, 4, 5] (fun x => 720 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c2 : PoolLB (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f <<< 720) p2ws p2g 9 :=
  poolFrom (tbl 6 0xfffffffefefaeee0) p19lb _ _ _ [0, 1, 6, 2, 3, 4, 5] (fun x => 720 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c3 : PoolLB (0x33333333333333333333333333333333 <<< 720) p2ws p2g 9 :=
  poolFrom (tbl 6 0xfffffffafefeaaa0) p21lb _ _ _ [0, 6, 1, 2, 3, 4, 5] (fun x => 720 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c4 : PoolLB (0x55555555555555555555555555555555 <<< 720) p2ws p2g 9 :=
  poolFrom (tbl 6 0xfffffffafefcaaa0) p22lb _ _ _ [6, 0, 1, 2, 3, 4, 5] (fun x => 720 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c5 : PoolLB (0xf000f000f000f000f000f000f000f <<< 720) p2ws p2g 7 :=
  poolFrom (tbl 5 0xfffeeae0) p8lb _ _ _ [0, 1, 5, 5, 2, 3, 4] (fun x => 720 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 16 + (x 3).toNat * 32 + (x 4).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c6 : PoolLB (0x5050505050505050505050505050505 <<< 720) p2ws p2g 7 :=
  poolFrom (tbl 5 0xfffeeca8) p23lb _ _ _ [5, 0, 5, 1, 2, 3, 4] (fun x => 720 + (x 0).toNat * 2 + (x 1).toNat * 8 + (x 2).toNat * 16 + (x 3).toNat * 32 + (x 4).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c7 : PoolLB (0xffffffffffffffff <<< 720) p2ws p2g 7 :=
  poolFrom (tbl 6 0xfffefffaeeeeee00) p24lb _ _ _ [0, 1, 2, 3, 4, 5, 6] (fun x => 720 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16 + (x 5).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c8 : PoolLB (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0 <<< 720) p2ws p2g 7 :=
  poolFrom (tbl 6 0xfffffffeffffeee0) p26lb _ _ _ [0, 1, 7, 2, 3, 4, 5] (fun x => 724 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c9 : PoolLB (0xffff0000ffff <<< 720) p2ws p2g 6 :=
  poolFrom (tbl 5 0xfffaee00) p28lb _ _ _ [0, 1, 2, 3, 5, 4, 5] (fun x => 720 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c10 : PoolLB (0xf0f0f0f0f0f0f0f <<< 720) p2ws p2g 6 :=
  poolFrom (tbl 5 0xfefaeee0) p29lb _ _ _ [0, 1, 5, 2, 3, 4, 5] (fun x => 720 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c11 : PoolLB (0xf0f0f0f000000000f0f0f0f <<< 720) p2ws p2g 6 :=
  poolFrom (tbl 5 0xfffeeee0) p31lb _ _ _ [0, 1, 5, 2, 3, 5, 4] (fun x => 720 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c12 : PoolLB (0xf0f0f0f000000000f0f0f0f0 <<< 720) p2ws p2g 6 :=
  poolFrom (tbl 5 0xfffeeee0) p31lb _ _ _ [0, 1, 6, 2, 3, 5, 4] (fun x => 724 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c13 : PoolLB (0xf000f00000000000f000f <<< 720) p2ws p2g 5 :=
  poolFrom (tbl 4 0xfee0) p9lb _ _ _ [0, 1, 4, 4, 2, 4, 3] (fun x => 720 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 16 + (x 3).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p2c14 : PoolLB (0x50505050000000005050505 <<< 720) p2ws p2g 5 :=
  poolFrom (tbl 4 0xfea8) p11lb _ _ _ [4, 0, 4, 1, 2, 4, 3] (fun x => 720 + (x 0).toNat * 2 + (x 1).toNat * 8 + (x 2).toNat * 16 + (x 3).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def p2hints : PCert := .node 0x101010101010101020202020202020201010101020103030303000303000303030301010101020202020202040404040404040401010101020202020303030305050505050505050101010102020202030303030503040404040504 [
  .node 0x101010102020202010101010201040404040101010102020202050505050101010102020202040404040504000c000c010101010202020204040404050505050009000000090101010102020202020204040404050505050505030303 [
    .node 0x10101010201010101010202020201010101020202020404040405040101010102020202040404040505050501010101020202020202040404040505050505050c0c0803080c0101010102020202020204040404050505050505030308030303090909 [],
    .node 0x1020405020205050c0c010101010202020204040404050505050303080909090809010101010202020204040404050505050308030309090808 [],
    .node 0x1010101020101010101020202020101010102020202040404040504010101010202020204040404050505050101010102020202040404040505050503080c0c0c080101010102020202020204040404050505050505090b09090009 [
      .node 0x10204050202050503080202050503030101 []
    ],
    .node 0x1020405020205050c0802020505030308090908080101010102020202040404040505050503030c030808090800 [
      .node 0x1020405020205050c080202050503030809 []
    ],
    .node 0x10204050202050502020505090c0c030901010202040405050303080c080c010101010202020204040404050505050b0b0b0c0c0808 [],
    .node 0x1020405020205050202050509080c08080303080c0808010101010202020204040404050505050c080008080c08 [
      .node 0x1020405020205050c0802020505080903030301 []
    ]
  ],
  .node 0x1010101020202020101010102010404040401010101020202020505050501010101020202020404040405040d08000000080101010102020202040404040505050509000b090b000101010102020202020204040404050505050505030303 [
    .node 0x10101010201010101010202020201010101020202020404040405040101010102020202040404040505050501010101020202020404040405050505080b0b0b0b0b0c03010101010b010202020202020b0002040404040b040505050505050b0005080b03030303030303090909 [
      .node 0x101010102010101010102020202010101010202020204040404010101010202020204040404080b0b0b0b0b0c030101010102020202040404040f0408070b0809050505 [],
      .node 0x101010101010101040404040504010101010404040405050505010101010404040405050505080b0b0b0b0b0c03010101010e01040404040505050508060b0809020202 []
    ],
    .node 0x10101010201010101010202020201010101020202020404040405040101010102020202040404040505050501010101020202020404040405050505080c030c0c080101010102020202020204040404050505050505090009090b09 [
      .node 0x10204050202050503080202050503030101 []
    ],
    .node 0x101010102010101010102020202010101010202020204040404050401010101020202020202040404040505050505050101010101010202020202020404040404040505050505050b0b090c030b0b0c010101010202020204040404050505050303090c0303030303080808 [],
    .node 0x10204050202050501010202040405050b0c0b0b0b0101010102020202040404040505050503030c08080808080101010102020202040404040505050503090c0c030303030808080c [],
    .node 0x101010102010101010102020202010101010202020204040404050401010101020202020202040404040505050505050101010102020202040404040505050503090c090b0b01010101020202020404040405050505080b08080d08 []
  ],
  .node 0x1010101020101010101020202020202010101010202020203030303010101010202020203030303050304040404050401010101020202020303030308030404040405050505010101010202020203030c03030304040404050505050808080808080c010101010101010108000101020202020202020208000202030303030303030308000303040404040404040408000404050505050505050508000505080808080c08 [
    .node 0x1010101020101010101020202020202010101010202020203030303010101010202020203030303080304040404010101010202020203030c030303040404040808080808080c010101010102020202030303030d03040404040f04080505050c050505 [],
    .node 0x10101010201010101010202020202020101010102020202030303030503010101010202020203030303080305050505010101010202020203030c03030305050505080808080801010101010202020203030303050505050505080404040c040404 [],
    .node 0x10101010201010101010202020201010101020202020404040405040101010102020202040404040505050501010101020202020404040405050505080808080c010101010102020202020204040404050505050505080303030303090c03030303 [],
    .node 0x10101010101010103030303010101010303030305030404040405040101010103030303080304040404050505050101010103030c03030304040404050505050808080808080c01010101010e01030303030d030404040405050505080202020c020202 [],
    .node 0x202020202020202020203030303020202020303030305030404040405040202020203030303080304040404050505050202020203030c0303030404040405050505080808080801020202020202030303030404040405050505080101010a010101 []
  ],
  .node 0x10101010201010101010202020202020101010102020202030303030101010102020202030303030503040404040504010101010202020202020303030303030000030404040405050505050501010101010102020202020203030003030304040404040405050505050508080c0c08080c01010101010101010202020202020202030303030000030303030303040404040404040405050505050505050c0c0c080808 [
    .node 0x10101010201010101010202020201010101020202020404040405040101010102020202040404040505050501010101020202020404040405050505080c0108010101010202020202020404040405050505050503090c030303030308030303 [],
    .node 0x1020405020205050101020204040505080c080c010101010202020204040404050505050c0c0808020205050c090c03030303030303 [],
    .node 0x102040502020505010101010202020204040404050505050c0c0101020204040505080c080c0808020205050c090c03090b0b0b0303 [],
    .node 0x1010101020101010101020202020101010102020202040404040504010101010101020202020202040404040404050505050505010101010202020204040404050505050808080101010102020202020204040404050505050505090c0b0b030b0c0b090c03030303030303 [],
    .node 0x10204050101020204040505010101010202020204040404050505050808010101010202020204040404050505050c08080808080c08020205050c0b0b0b0b0c090c03030303030303 []
  ],
  .node 0x101010102010101010102020202020201010101020202020303030301010101020202020303030305030404040405040101010102020202030303030d03040404040505050501010101010102020202020203030c03030304040404040405050505050508080c0c0c080801010101010101010202020202020202030303030c00030303030303040404040404040405050505050505050c000c080808 [
    .node 0x102020203050405010102020c03040405050202030303080d050501080808010101010202020203030d0d03030303040404040505050508080101 [],
    .node 0x10101010201010101010202020201010101020202020404040405040101010102020202040404040505050501010101020202020404040405050505080c010c0c0801010101020202020202040404040505050505050c000c0b0b0b [
      .node 0x10204050202050501080202050503030101 []
    ]
  ],
  .node 0x1010101020101010101020202020202010101010202020203030303010101010202020203030303050304040404050401010101020202020202030303030303080003040404040505050505050101010102020202030300030303040404040505050508080c080808080101010101010101020202020202020203030303030303030800030304040404040404040505050505050505080808080008 [
    .node 0x1020202030504050202030303080d0505010102020c0304040505010c0808010101010202020203030d0d030303030404040405050505080c0101 [],
    .node 0x10101010201010101010202020201010101020202020404040405040101010102020202040404040505050501010101020202020404040405050505010808080101010102020202020204040404050505050505080303030303030303090303 [],
    .node 0x102040502020505010101010202020204040404050505050808080c0808080c0202050508090c0808080c000303 [
      .node 0x1020405020205050c0802020505080903030301 []
    ],
    .node 0x10101010201010101010202020201010101020202020404040405040101010102020202040404040505050501010101020202020404040405050505080d080101010102020202020204040404050505050505090c03090b0b08080b []
  ]
]

theorem p2lb : LB (tbl 7 0xffffffffffffffeefffefffaeeeeee00) 11 := by
  apply finishPool (tbl 7 0xffffffffffffffeefffefffaeeeeee00) p2ws p2g 360 10 p2pts p2ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p2g % (2^360) = 0 ∧ (p2g >>> 360) % (2^360) = 2^360-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p2ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p2c0⟩
    · exact ⟨by decide +kernel, p2c1⟩
    · exact ⟨by decide +kernel, p2c2⟩
    · exact ⟨by decide +kernel, p2c3⟩
    · exact ⟨by decide +kernel, p2c4⟩
    · exact ⟨by decide +kernel, p2c5⟩
    · exact ⟨by decide +kernel, p2c6⟩
    · exact ⟨by decide +kernel, p2c7⟩
    · exact ⟨by decide +kernel, p2c8⟩
    · exact ⟨by decide +kernel, p2c9⟩
    · exact ⟨by decide +kernel, p2c10⟩
    · exact ⟨by decide +kernel, p2c11⟩
    · exact ⟨by decide +kernel, p2c12⟩
    · exact ⟨by decide +kernel, p2c13⟩
    · exact ⟨by decide +kernel, p2c14⟩
  · decide +kernel
  · apply ptop_at_root (by decide +kernel)
    apply certCheck_sound _ _ _ _ _ _ _ _ p2hints
    decide +kernel

theorem p36lb : LB (tbl 3 0xa8) 2 := 
  rule2 (tbl 3 0xa8) 1 0 1 0 5 0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _)

theorem p37lb : LB (tbl 3 0xf8) 2 := 
  rule2 (tbl 3 0xf8) 0 0 2 0 4 0 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _)

theorem p35lb : LB (tbl 4 0xeec0) 4 := 
  rule2 (tbl 4 0xeec0) 0 2 8 0 6 0 6 (by decide +kernel) (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 4 0xeec0) 0 false) (tbl 3 0xa8) [3, 0, 1, 2] (by decide +kernel) p36lb) (pullLB (rs (tbl 4 0xeec0) 0 true) (tbl 3 0xf8) [4, 0, 1, 2] (by decide +kernel) p37lb)

theorem p38lb : LB (tbl 4 0xfac0) 4 := 
  pullLB (tbl 4 0xfac0) (tbl 4 0xeec0) [0, 2, 1, 3] (by decide +kernel) p35lb

theorem p39lb : LB (tbl 4 0xeae0) 4 := 
  pullLB (tbl 4 0xeae0) (tbl 4 0xeec0) [1, 0, 3, 2] (by decide +kernel) p35lb

theorem p40lb : LB (tbl 4 0xeea0) 4 := 
  pullLB (tbl 4 0xeea0) (tbl 4 0xeec0) [1, 0, 2, 3] (by decide +kernel) p35lb

theorem p41lb : LB (tbl 4 0xeca8) 4 := 
  pullLB (tbl 4 0xeca8) (tbl 4 0xeec0) [3, 1, 0, 2] (by decide +kernel) p35lb

def p34ws : List ℕ := [0x2aaaaaaa955530ad2a2def89bf62aff5000000000001ff807fe01fe0, 0x33333333262fad4a355644d2fbbff252801ff800000000007fffe000, 0x3c3c3c3c3889c673f998f6ffd235349880000007fe01ffff80000000, 0x3fc03fc03f3e0b83beff872323c9c8e37fe00007fffe000000000000, 0x3fffc0003fcff3ffc0e0f83c3c0e0f0c7ffffff80000000000000000]
def p34g : ℕ := 0x3fbebbb03fffffffffffffffffffffff800000000000000000000000
def p34pts := packedSample 5 95 0x6318c6318c631294a5294a5294210842108318c6318c631884210842105294a5294a5290842108420c6318c6318c621084210841084210842000000 0x7bbcdeb348a93edeaf6a4e2a37359b56938fbbca3dcd524dcd65cd5a93dbd6917b527372d5a39a736ef38bd6a49cdab4dcb51cd9ace2d5a4f48a926
def p34ds : List (ℕ × ℕ) := [(0xffff <<< 190, 4), (0xff00ff <<< 190, 4), (0xf0f0f0f <<< 190, 4), (0x33333333 <<< 190, 4), (0x55555555 <<< 190, 4)]
theorem p34c0 : PoolLB (0xffff <<< 190) p34ws p34g 4 :=
  poolFrom (tbl 4 0xeec0) p35lb _ _ _ [0, 1, 2, 3, 4] (fun x => 190 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p34c1 : PoolLB (0xff00ff <<< 190) p34ws p34g 4 :=
  poolFrom (tbl 4 0xfac0) p38lb _ _ _ [0, 1, 2, 4, 3] (fun x => 190 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p34c2 : PoolLB (0xf0f0f0f <<< 190) p34ws p34g 4 :=
  poolFrom (tbl 4 0xeae0) p39lb _ _ _ [0, 1, 4, 2, 3] (fun x => 190 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p34c3 : PoolLB (0x33333333 <<< 190) p34ws p34g 4 :=
  poolFrom (tbl 4 0xeea0) p40lb _ _ _ [0, 4, 1, 2, 3] (fun x => 190 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p34c4 : PoolLB (0x55555555 <<< 190) p34ws p34g 4 :=
  poolFrom (tbl 4 0xeca8) p41lb _ _ _ [4, 0, 1, 2, 3] (fun x => 190 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem p34lb : LB (tbl 5 0xfefaeec0) 7 := by
  apply finishPool (tbl 5 0xfefaeec0) p34ws p34g 95 6 p34pts p34ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p34g % (2^95) = 0 ∧ (p34g >>> 95) % (2^95) = 2^95-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p34ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p34c0⟩
    · exact ⟨by decide +kernel, p34c1⟩
    · exact ⟨by decide +kernel, p34c2⟩
    · exact ⟨by decide +kernel, p34c3⟩
    · exact ⟨by decide +kernel, p34c4⟩
  · decide +kernel
  · decide +kernel

theorem p42lb : LB (tbl 5 0xfefeeea0) 6 := 
  pullLB (tbl 5 0xfefeeea0) (tbl 5 0xfefaeee0) [0, 1, 4, 3, 2] (by decide +kernel) p29lb

theorem p43lb : LB (tbl 5 0xfefefa00) 5 := 
  rule1 (tbl 5 0xfefefa00) 0 false 4 8 0 12 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 5 0xfefefa00) 0 false) (tbl 4 0xeec0) [4, 0, 1, 2, 3] (by decide +kernel) p35lb)

theorem p44lb : LB (tbl 5 0xfeeefe00) 5 := 
  pullLB (tbl 5 0xfeeefe00) (tbl 5 0xfefefa00) [0, 2, 1, 4, 3] (by decide +kernel) p43lb

def p33ws : List ℕ := [0x2aaaaaaaaaaaaaaa8952492a09348a944aa424c457deec889fee892f7bc44fff9280000000000000000000000003fff8003fff001fff800fff00, 0x3333333333333333126492341259132094defe88a5ef77fdc444124fbdbff889240000000000000000003fff8003ffffffc000001ffffff00000, 0x3c3c3c3c3c3c3c3c23813fb9a4621c492708471139f7bbdefef77ff2110891120900007fff000000000000000003ffffffffffffe00000000000, 0x3fc03fc03fc03fc03c0823c0c783ff8e381f77fffe843d10e887a47421d11a23c1800000000007fff8003ffffffc000000000000000000000000, 0x3fffc0003fffc0003ff1fc017803dff3fff07821c107c21f10f847883e21e43c0e7fff80000007ffffffc0000000000000000000000000000000, 0x3fffffffc00000003ffe3ffe7fffe003c01f803e01f803e01f00780fc03e07c0707ffffffffff800000000000000000000000000000000000000]
def p33g : ℕ := 0x3fffbffbbfbfbe803fffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000
def p33pts := packedSample 6 199 0x30c30c30c30c30c30c30c30c2492492492492492492492482082082082082082081861861861861861861861861041041041041041041028a28a28a28a28a28a28a2882082082082082082081c71c71c71c71c71c71c71c61861861861861861861451451451451451451451041041041041041030c30c30c30c30c30c30c2082082082082082041041041041041041000000000000 0x3ceb9e36d74cf2c688a151247cdb5d2eb6ca279a58a150ce34cb1b2aa689a58e287ceb9e2879d71b69951244c278d32c5c699595513491eaeaeaa2279b6923ce30b278b2aa6871a64e34c2c9def9e69637d75954cf38d2f6ba79a279759448f38cd6d9e585d5d55113cd309d2c9a571655438d333ae78e285b5d34913cb272aa68e26964d238bc6996385955344d2c9a22854491309
def p33ds : List (ℕ × ℕ) := [(0x5555555555555555 <<< 398, 7), (0xffff0000ffff <<< 398, 6), (0xf0f0f0f0f0f0f0f <<< 398, 6), (0x3333333333333333 <<< 398, 6), (0xf0f00000f0f <<< 398, 5), (0x333300003333 <<< 398, 5), (0x303030303030303 <<< 398, 5), (0xffffffff <<< 398, 5), (0xff00ff00ff00ff <<< 398, 5), (0xf0f0f0f <<< 398, 4), (0x33003300330033 <<< 398, 4)]
theorem p33c0 : PoolLB (0x5555555555555555 <<< 398) p33ws p33g 7 :=
  poolFrom (tbl 5 0xfefaeec0) p34lb _ _ _ [5, 0, 1, 2, 3, 4] (fun x => 398 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p33c1 : PoolLB (0xffff0000ffff <<< 398) p33ws p33g 6 :=
  poolFrom (tbl 5 0xffeefa00) p16lb _ _ _ [0, 1, 2, 3, 5, 4] (fun x => 398 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p33c2 : PoolLB (0xf0f0f0f0f0f0f0f <<< 398) p33ws p33g 6 :=
  poolFrom (tbl 5 0xfefeeea0) p42lb _ _ _ [0, 1, 5, 2, 3, 4] (fun x => 398 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p33c3 : PoolLB (0x3333333333333333 <<< 398) p33ws p33g 6 :=
  poolFrom (tbl 5 0xfefaeee0) p29lb _ _ _ [0, 5, 1, 2, 3, 4] (fun x => 398 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p33c4 : PoolLB (0xf0f00000f0f <<< 398) p33ws p33g 5 :=
  poolFrom (tbl 4 0xfea0) p10lb _ _ _ [0, 1, 4, 2, 4, 3] (fun x => 398 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p33c5 : PoolLB (0x333300003333 <<< 398) p33ws p33g 5 :=
  poolFrom (tbl 4 0xfae0) p17lb _ _ _ [0, 4, 1, 2, 4, 3] (fun x => 398 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p33c6 : PoolLB (0x303030303030303 <<< 398) p33ws p33g 5 :=
  poolFrom (tbl 4 0xeea8) p30lb _ _ _ [0, 4, 4, 1, 2, 3] (fun x => 398 + (x 0).toNat * 1 + (x 1).toNat * 8 + (x 2).toNat * 16 + (x 3).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p33c7 : PoolLB (0xffffffff <<< 398) p33ws p33g 5 :=
  poolFrom (tbl 5 0xfefefa00) p43lb _ _ _ [0, 1, 2, 3, 4, 5] (fun x => 398 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p33c8 : PoolLB (0xff00ff00ff00ff <<< 398) p33ws p33g 5 :=
  poolFrom (tbl 5 0xfeeefe00) p44lb _ _ _ [0, 1, 2, 5, 3, 4] (fun x => 398 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p33c9 : PoolLB (0xf0f0f0f <<< 398) p33ws p33g 4 :=
  poolFrom (tbl 4 0xeea0) p40lb _ _ _ [0, 1, 4, 2, 3, 4] (fun x => 398 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p33c10 : PoolLB (0x33003300330033 <<< 398) p33ws p33g 4 :=
  poolFrom (tbl 4 0xeae0) p39lb _ _ _ [0, 4, 1, 4, 2, 3] (fun x => 398 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 16 + (x 3).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def p33hints : PCert := .node 0x20002000000000200000200030003020305020003000300040004020406020004000403040703010101010101010101010101010101010101010101010101 [
  .node 0x1010b000606040002020407010109040404000b000b02060602030707030101010104040409 [
    .node 0x0 [],
    .node 0x0 [],
    .node 0xb [],
    .node 0x4 []
  ],
  .node 0x10109000606010104040904000900090206060606090002030707030101010104040409 [
    .node 0x1010101 [],
    .node 0x0 [],
    .node 0x4 [],
    .node 0x0 []
  ],
  .node 0x10106060400010108040404020606020b00000b030707030101010104040408 [
    .node 0x0 [],
    .node 0x0 [],
    .node 0xb []
  ],
  .node 0x101060602020407010104040804020606020b080008030707030101010104040408 [
    .node 0x0 []
  ],
  .node 0x101050503000101090303030a00000a02050502040707040101010103030309 [
    .node 0x0 [],
    .node 0x0 [],
    .node 0xa []
  ],
  .node 0x1010505020203070101030309030a09000902050502040707040101010103030309 [
    .node 0x0 []
  ],
  .node 0x10105050a0002020300030701010803030302050502000a000a040707040101010103030308 [
    .node 0x0 [],
    .node 0x0 [],
    .node 0xa [],
    .node 0x3 []
  ],
  .node 0x10105050800010103030803020505050508000200080008040707040101010103030308 [
    .node 0x0 [],
    .node 0x3 [],
    .node 0x1010101 [],
    .node 0x0 []
  ],
  .node 0x10101010200020504020101000005050606010102090202000000000305000005030505040606040101010102090202 [
    .node 0x1010101 [],
    .node 0x3 [],
    .node 0x0 [
      .node 0x0 []
    ],
    .node 0x500060001 [
      .node 0x0 [],
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x2 [],
    .node 0x500 [
      .node 0x0 []
    ],
    .node 0x2 [
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 [],
        .node 0x0 [],
        .node 0x0 []
      ]
    ],
    .node 0x2 [],
    .node 0x5000600 [
      .node 0x0 [],
      .node 0x0 [
        .node 0x0 [],
        .node 0x0 [],
        .node 0x0 []
      ]
    ]
  ],
  .node 0x1010101000905050606010102020902000900090305050304060606060900040101010102090202 [
    .node 0x1010101 [],
    .node 0x2 [],
    .node 0x0 [],
    .node 0x0 []
  ],
  .node 0x101010108000900080808090208000800080002030800080a080003040800080b080004010101010108000108080908 [
    .node 0x8000900080808090a000b00 [
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ]
    ],
    .node 0x1010800090008080101 [
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ]
    ],
    .node 0x1010101 [],
    .node 0x1010800090008090101 [
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ]
    ],
    .node 0x1010101 [],
    .node 0x1010101 [],
    .node 0x0 [],
    .node 0x101010102020202 [],
    .node 0x2 [
      .node 0x0 [
        .node 0x0 [],
        .node 0x0 [],
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ]
    ],
    .node 0x2 [
      .node 0x0 [
        .node 0x0 [],
        .node 0x0 [],
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ]
    ]
  ],
  .node 0x10101010000010100000101080908090200000203000003040000040101010109090808 [
    .node 0x0 [],
    .node 0x0 [],
    .node 0x0 [],
    .node 0x0 [],
    .node 0x500060001 [
      .node 0x0 [],
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x4 [],
    .node 0x0 [],
    .node 0x3 [],
    .node 0x0 []
  ],
  .node 0x10101010000090b010108090908020900020309000304090b040101010100090808 [
    .node 0x0 [],
    .node 0x0 [],
    .node 0x5 [
      .node 0x0 []
    ],
    .node 0x2 [],
    .node 0x0 []
  ],
  .node 0x1010101080a01010000080908080208000203080a03040800040101010108080008 [
    .node 0x0 [],
    .node 0x0 [],
    .node 0x6 [
      .node 0x0 []
    ],
    .node 0x2 [],
    .node 0x0 []
  ],
  .node 0x10101010000050506060101020003020206010108020202000000000305050304060000060406060101010102020208 [
    .node 0x1010101 [],
    .node 0x4 [],
    .node 0x0 [
      .node 0x0 []
    ],
    .node 0x500060001 [
      .node 0x0 [],
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x2 [],
    .node 0x600 [
      .node 0x0 []
    ],
    .node 0x6000500 [
      .node 0x0 [],
      .node 0x0 [
        .node 0x0 [],
        .node 0x0 [],
        .node 0x0 []
      ]
    ],
    .node 0x2 [
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 [],
        .node 0x0 [],
        .node 0x0 []
      ]
    ],
    .node 0x2 []
  ],
  .node 0x1010101000805050606010102020802000800080305050505080003040606040101010102020208 [
    .node 0x1010101 [],
    .node 0x2 [],
    .node 0x0 [],
    .node 0x0 []
  ]
]

theorem p33lb : LB (tbl 6 0xfffeffeefefefa00) 9 := by
  apply finishPool (tbl 6 0xfffeffeefefefa00) p33ws p33g 199 8 p33pts p33ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p33g % (2^199) = 0 ∧ (p33g >>> 199) % (2^199) = 2^199-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p33ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p33c0⟩
    · exact ⟨by decide +kernel, p33c1⟩
    · exact ⟨by decide +kernel, p33c2⟩
    · exact ⟨by decide +kernel, p33c3⟩
    · exact ⟨by decide +kernel, p33c4⟩
    · exact ⟨by decide +kernel, p33c5⟩
    · exact ⟨by decide +kernel, p33c6⟩
    · exact ⟨by decide +kernel, p33c7⟩
    · exact ⟨by decide +kernel, p33c8⟩
    · exact ⟨by decide +kernel, p33c9⟩
    · exact ⟨by decide +kernel, p33c10⟩
  · decide +kernel
  · apply ptop_at_root (by decide +kernel)
    apply certCheck_sound _ _ _ _ _ _ _ _ p33hints
    decide +kernel

theorem p45lb : LB (tbl 6 0xfffefffefefefae0) 9 := 
  pullLB (tbl 6 0xfffefffefefefae0) (tbl 6 0xfffffffefefaeee0) [0, 1, 5, 4, 3, 2] (by decide +kernel) p19lb

theorem p47lb : LB (tbl 5 0xfefeeee8) 8 := 
  pullLB (tbl 5 0xfefeeee8) (tbl 5 0xfffeeea8) [0, 4, 1, 2, 3] (by decide +kernel) p20lb

theorem p46lb : LB (tbl 6 0xfffefffafefefea0) 9 := 
  rule1 (tbl 6 0xfffefffafefefea0) 1 false 8 8 0 5 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 6 0xfffefffafefefea0) 1 false) (tbl 5 0xfefeeee8) [0, 5, 1, 2, 3, 4] (by decide +kernel) p47lb)

theorem p49lb : LB (tbl 5 0xfffafca0) 7 := 
  pullLB (tbl 5 0xfffafca0) (tbl 5 0xfffaeea0) [2, 1, 0, 3, 4] (by decide +kernel) p13lb

theorem p50lb : LB (tbl 5 0xfefafea0) 7 := 
  pullLB (tbl 5 0xfefafea0) (tbl 5 0xfffaeea0) [0, 1, 4, 3, 2] (by decide +kernel) p13lb

theorem p51lb : LB (tbl 5 0xfefeeec8) 7 := 
  pullLB (tbl 5 0xfefeeec8) (tbl 5 0xfffeeae0) [0, 4, 1, 3, 2] (by decide +kernel) p8lb

theorem p52lb : LB (tbl 5 0xfefefca0) 6 := 
  pullLB (tbl 5 0xfefefca0) (tbl 5 0xfefaeee0) [4, 1, 0, 3, 2] (by decide +kernel) p29lb

theorem p53lb : LB (tbl 5 0xfefceee0) 6 := 
  pullLB (tbl 5 0xfefceee0) (tbl 5 0xfefaeee0) [1, 0, 2, 3, 4] (by decide +kernel) p29lb

def p48ws : List ℕ := [0x2aaaaaaaaaaaaaaa89524926092c8a904abefea22a2223112ffdd892fffc92000000000000000000ffff00000000001fffc003ffe00, 0x33333333333333331260bfb59249132494c424c453f776224bdef7ff8898240001fffc000000000000000007fff8001ffffffc00000, 0x3c3c3c3c3c3c3c3c2385123824721c49270847289cffbbfffc889924912d4a00000000000000000000000007ffffffe000000000000, 0x3fc03fc03fc03fc03c0823c0c783ff8e381f77dfff443c447110e24722320c00000000001fffe000fffffff80000000000000000000, 0x3fffc0003fffc0003ff1fc017803dff3fff07810e087c087821f047843c071fffe0000001fffffff000000000000000000000000000, 0x3fffffffc00000003ffe3ffe7fffe003c01f801f00f800f803e007807c0381ffffffffffe0000000000000000000000000000000000]
def p48g : ℕ := 0x3fffbffebfbfbf283ffffffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000000000
def p48pts := packedSample 6 181 0x30c30c30c30c30c30c30c30c228a28a28a28a28a28a28a28208208208208208208186186186186186186186186104104104104104104102492492492492492492492492082082082082082082061861861861861861861861841041041041041041041030c30c30c30c30c30c30c3082082082082082082041041041041041041040000000000000 0x3ceb9e36d74cf2c6892151247adb3caeaeaa279a48e148ae34cb1b2aa689a592387ceb9e2879d71b69951244c2b8d32c5c699595513491e6dae9a2175b6513cd30b285e2caa9a1c69938d30b2b6ba79a479759448f38c287174b2696471655438d307173ae78e16d74d244f2ca1c5caa9a36964d238b287c6996385955344d2c716892151244c285
def p48ds : List (ℕ × ℕ) := [(0xffff0000ffff <<< 362, 7), (0xff00ff00ff00ff <<< 362, 7), (0xf0f0f0f0f0f0f0f <<< 362, 7), (0x3333333333333333 <<< 362, 7), (0xffffffff <<< 362, 6), (0x5555555555555555 <<< 362, 6)]
theorem p48c0 : PoolLB (0xffff0000ffff <<< 362) p48ws p48g 7 :=
  poolFrom (tbl 5 0xfffafca0) p49lb _ _ _ [0, 1, 2, 3, 5, 4] (fun x => 362 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p48c1 : PoolLB (0xff00ff00ff00ff <<< 362) p48ws p48g 7 :=
  poolFrom (tbl 5 0xfefafea0) p50lb _ _ _ [0, 1, 2, 5, 3, 4] (fun x => 362 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p48c2 : PoolLB (0xf0f0f0f0f0f0f0f <<< 362) p48ws p48g 7 :=
  poolFrom (tbl 5 0xfefaeec0) p34lb _ _ _ [0, 1, 5, 2, 3, 4] (fun x => 362 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p48c3 : PoolLB (0x3333333333333333 <<< 362) p48ws p48g 7 :=
  poolFrom (tbl 5 0xfefeeec8) p51lb _ _ _ [0, 5, 1, 2, 3, 4] (fun x => 362 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p48c4 : PoolLB (0xffffffff <<< 362) p48ws p48g 6 :=
  poolFrom (tbl 5 0xfefefca0) p52lb _ _ _ [0, 1, 2, 3, 4, 5] (fun x => 362 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p48c5 : PoolLB (0x5555555555555555 <<< 362) p48ws p48g 6 :=
  poolFrom (tbl 5 0xfefceee0) p53lb _ _ _ [5, 0, 1, 2, 3, 4] (fun x => 362 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def p48hints : PCert := .node 0x101010102020202010101010303030301010101020202020404040401010101020202020303030303030506000501010101020202020303030304040404 [
  .node 0x3030101030302020303050605050101010102020202030303030404040405060505 []
]

theorem p48lb : LB (tbl 6 0xfffefffafefefca0) 9 := by
  apply finishPool (tbl 6 0xfffefffafefefca0) p48ws p48g 181 8 p48pts p48ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p48g % (2^181) = 0 ∧ (p48g >>> 181) % (2^181) = 2^181-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p48ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p48c0⟩
    · exact ⟨by decide +kernel, p48c1⟩
    · exact ⟨by decide +kernel, p48c2⟩
    · exact ⟨by decide +kernel, p48c3⟩
    · exact ⟨by decide +kernel, p48c4⟩
    · exact ⟨by decide +kernel, p48c5⟩
  · decide +kernel
  · apply ptop_at_root (by decide +kernel)
    apply certCheck_sound _ _ _ _ _ _ _ _ p48hints
    decide +kernel

theorem p55lb : LB (tbl 5 0xfefefae0) 7 := 
  pullLB (tbl 5 0xfefefae0) (tbl 5 0xfffeeae0) [0, 1, 4, 3, 2] (by decide +kernel) p8lb

def p54ws : List ℕ := [0xaaaaaaaaaaaaaaaa2544892a4498496422a226f7bb2127bde227dfd115ffe2500000000000000000000007fff0007ffe003fff001ffe00, 0xcccccccccccccccc4988124dfed4924843444b7bddf7b908844beeeffe2244200000001fffc00000000007ffffff8000003fffffe00000, 0xf0f0f0f0f0f0f0f08e11247088e1239ef7888c7deefbf7dedffc84822844888000000000000001fffe0007ffffffffffffc00000000000, 0xff00ff00ff00ff00f02247810f063c1f7bffffa10f423a10e88d08f44e88f13000000000000001fffffff8000000000000000000000000, 0xffff0000ffff0000ffc3f801effbfff07c10f041f083c41f10f20f08710f01cffff8001ffffffe00000000000000000000000000000000, 0xffffffff00000000fffc7ffff003c01f801f007e00fc07e01f03f00f81f01e0fffffffe000000000000000000000000000000000000000]
def p54g : ℕ := 0xfffefffefffaee00fffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000
def p54pts := packedSample 6 188 0xc30c30c30c30c30c30c30c30c2082082082082082082081249249249249249249249241041041041041041040c30c30c30c30c30c30c30c3082082082082082082082071c71c71c71c71c71c71c71861861861861861861851451451451451451451441041041041041040c30c30c30c30c30c30c3082082082082082081041041041041041040000000000000 0xf3ae78db5d33cb1a248a1614478d32c6caa9a269648e287adb3ca279b6985d651344ae34cb171a65859551347cbadb2891e75c6143ce34a278b2aa6871a65838d2ca277be79a58df5d65533ce34bdae9e69227975943ce2b5b6796485d5d55113cd274b2696471655438dceb9e38a16d74d13cb289caa9a389a59338b2b1a658e16554d134b268922858511289
def p54ds : List (ℕ × ℕ) := [(0xf0f0f0f0f0f0f0f <<< 376, 7)]
theorem p54c0 : PoolLB (0xf0f0f0f0f0f0f0f <<< 376) p54ws p54g 7 :=
  poolFrom (tbl 5 0xfefefae0) p55lb _ _ _ [0, 1, 5, 2, 3, 4] (fun x => 376 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem p54lb : LB (tbl 6 0xfffefffefffaee00) 8 := by
  apply finishPool (tbl 6 0xfffefffefffaee00) p54ws p54g 188 7 p54pts p54ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p54g % (2^188) = 0 ∧ (p54g >>> 188) % (2^188) = 2^188-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p54ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl
    · exact ⟨by decide +kernel, p54c0⟩
  · decide +kernel
  · decide +kernel

theorem p56lb : LB (tbl 6 0xfffeffeefffeee00) 8 := 
  rule1 (tbl 6 0xfffeffeefffeee00) 0 false 7 8 0 10 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 6 0xfffeffeefffeee00) 0 false) (tbl 5 0xfefafea0) [5, 0, 1, 2, 3, 4] (by decide +kernel) p50lb)

def p32ws : List ℕ := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa112a22222540889a212a24224a88224c1092c421150844df7deec42127fef78444fdf7f42115ffff889400000000000000000000000000000000000000000000003fffff00001ffffe0001fffff00007fffe000, 0xcccccccccccccccccccccccccccccccc224c44444681112c424c4044937dff6a212488421a10896fbef77ff7b8842208897efbbbfffe1089110800000000000000000000000001fffff8000000000000003fffffffffe000000001fffffffff80000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0447009ff77322230847088891c10447042473ef7bc21118fdf7bbefbf7df7b7fff882120422821120220000007ffffc0000000000000000000000000fffffc00003ffffffffffffffffffe00000000000000000, 0xff00ff00ff00ff00ff00ff00ff00ff0087809088780443c107811111e020878284783ffbdffffff20843c842390843911190423c844e4223a44c000000000000000000000000000000000000ffffffffffc000000000000000000000000000000000000, 0xffff0000ffff0000ffff0000ffff0000f801010f80187c01fffe1e1e007ef7fdffffd083e0421e04107c1083c2107c221e2083c10870843c40700000000000000007fffff00001ffffffffff00000000000000000000000000000000000000000000000, 0xffffffff00000000ffffffff00000000fffe1ff0002f8001f7ffe3ffffc0f801078020fc0083e0081f8020fc041f8043e040fc020f8107c00783fffff80000000007fffffffffe000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffff0000000000000000ffffe1ffffcffffff80003e0007f0001f8003f0000fc000fe0003f0007e0007c007f0003f001f8007803fffffffffffffff80000000000000000000000000000000000000000000000000000000000000000000]
def p32g : ℕ := 0xfffffffeffffffeefffefffefffaee00fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000
def p32pts := packedSample 7 334 0x3060c183060c183060c183060c183060c183060c11224489122448912244891224489122448912040810204081020408102040810204080c183060c183060c183060c183060c183060c1830408102040810204081020408102040810122448912244891224489122448912244891224408102040810204081020408102040810183060c183060c183060c183060c183060c1830408102040810204081020408102040810203870e1c3870e1c3870e1c3870e1c3870e1c3870c183060c183060c183060c183060c183050a142850a142850a142850a142850a142840810204081020408102040810203060c183060c183060c183060c183060c183040810204081020408102040810204040810204081020408102040810204080000000000000000000000 0x3c74e5c786cd5a7466cb931e2c34244282a122243d3666cb92e56ab5284e9b324478d161414853868c98b0d8a94a8d0992a4c88d161c283e3a72e3c283c74e5c366ad19b262a12224260a11e1a3262c2e1a3262b152950992a446890f2b55a9d2a109d3666c911e3668c172c5099115c2c54a54683868c989c3464c162a50991d97274d9921e2e5ab14243c74e18283c70d1427458992a4c870b15295070d19303868b14273d79f1e34586dd7a74c9519f2e58a931e3868bcd5a7478d09b2e4e992223c5cb141e38565ab363c582d56a74a9109d2e54a111e344e4a93234568b13254870b1528386e3a72e3c385059ab4e8d121365c9911e2c509c54a546870992a4c8d11a2c4c70b15868c98b0e0b152951a132549911a2c4d0910a0a848890982844509
def p32ds : List (ℕ × ℕ) := [(0xffffffff00000000ffffffff <<< 668, 9), (0xff00ff00ff00ff00ff00ff00ff00ff <<< 668, 9), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f <<< 668, 9), (0x33333333333333333333333333333333 <<< 668, 9), (0x55555555555555555555555555555555 <<< 668, 9), (0xffffffffffffffff <<< 668, 8), (0xffff0000ffff0000ffff0000ffff <<< 668, 8)]
theorem p32c0 : PoolLB (0xffffffff00000000ffffffff <<< 668) p32ws p32g 9 :=
  poolFrom (tbl 6 0xffffffeefffaee00) p3lb _ _ _ [0, 1, 2, 3, 4, 6, 5] (fun x => 668 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p32c1 : PoolLB (0xff00ff00ff00ff00ff00ff00ff00ff <<< 668) p32ws p32g 9 :=
  poolFrom (tbl 6 0xfffeffeefefefa00) p33lb _ _ _ [0, 1, 2, 6, 3, 4, 5] (fun x => 668 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p32c2 : PoolLB (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f <<< 668) p32ws p32g 9 :=
  poolFrom (tbl 6 0xfffefffefefefae0) p45lb _ _ _ [0, 1, 6, 2, 3, 4, 5] (fun x => 668 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p32c3 : PoolLB (0x33333333333333333333333333333333 <<< 668) p32ws p32g 9 :=
  poolFrom (tbl 6 0xfffefffafefefea0) p46lb _ _ _ [0, 6, 1, 2, 3, 4, 5] (fun x => 668 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p32c4 : PoolLB (0x55555555555555555555555555555555 <<< 668) p32ws p32g 9 :=
  poolFrom (tbl 6 0xfffefffafefefca0) p48lb _ _ _ [6, 0, 1, 2, 3, 4, 5] (fun x => 668 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p32c5 : PoolLB (0xffffffffffffffff <<< 668) p32ws p32g 8 :=
  poolFrom (tbl 6 0xfffefffefffaee00) p54lb _ _ _ [0, 1, 2, 3, 4, 5, 6] (fun x => 668 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16 + (x 5).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p32c6 : PoolLB (0xffff0000ffff0000ffff0000ffff <<< 668) p32ws p32g 8 :=
  poolFrom (tbl 6 0xfffeffeefffeee00) p56lb _ _ _ [0, 1, 2, 3, 6, 4, 5] (fun x => 668 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def p32hints : PCert := .node 0x10101010607000601010101020202020101010102020202030303030101010103030303020202020202040404040101010104040404020202020303030305050505010101010505050502020202030303030503040404040504 [
  .node 0x1010101010101010202020202020101010102020202030303030101010102020202030303030503040404040504010101010202020202020303030303030404040405050505050501010101020202020202030303030404040404040505050505050606060706060601010101010101010202020202020202030303030303030304040404040404040505050505050505060607060606 []
]

theorem p32lb : LB (tbl 7 0xfffffffeffffffeefffefffefffaee00) 11 := by
  apply finishPool (tbl 7 0xfffffffeffffffeefffefffefffaee00) p32ws p32g 334 10 p32pts p32ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p32g % (2^334) = 0 ∧ (p32g >>> 334) % (2^334) = 2^334-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p32ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p32c0⟩
    · exact ⟨by decide +kernel, p32c1⟩
    · exact ⟨by decide +kernel, p32c2⟩
    · exact ⟨by decide +kernel, p32c3⟩
    · exact ⟨by decide +kernel, p32c4⟩
    · exact ⟨by decide +kernel, p32c5⟩
    · exact ⟨by decide +kernel, p32c6⟩
  · decide +kernel
  · apply ptop_at_root (by decide +kernel)
    apply certCheck_sound _ _ _ _ _ _ _ _ p32hints
    decide +kernel

theorem p59lb : LB (tbl 5 0xfefeeae0) 7 := 
  pullLB (tbl 5 0xfefeeae0) (tbl 5 0xfffaeea0) [3, 2, 0, 1, 4] (by decide +kernel) p13lb

theorem p60lb : LB (tbl 5 0xfefeeca0) 7 := 
  pullLB (tbl 5 0xfefeeca0) (tbl 5 0xfffaeca0) [0, 3, 2, 1, 4] (by decide +kernel) p15lb

theorem p61lb : LB (tbl 5 0xfffeee00) 6 := 
  rule1 (tbl 5 0xfffeee00) 0 false 5 8 0 10 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 5 0xfffeee00) 0 false) (tbl 4 0xfea0) [4, 0, 1, 2, 3] (by decide +kernel) p10lb)

theorem p63lb : LB (tbl 4 0xfeec) 5 := 
  pullLB (tbl 4 0xfeec) (tbl 4 0xfef8) [0, 2, 1, 3] (by decide +kernel) p14lb

theorem p62lb : LB (tbl 5 0xfffefefa) 6 := 
  rule1 (tbl 5 0xfffefefa) 0 false 5 0 0 4 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 5 0xfffefefa) 0 false) (tbl 4 0xfeec) [4, 0, 1, 2, 3] (by decide +kernel) p63lb)

theorem p64lb : LB (tbl 5 0xfefaee00) 5 := 
  rule1 (tbl 5 0xfefaee00) 1 false 4 8 0 9 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 5 0xfefaee00) 1 false) (tbl 4 0xeea0) [0, 4, 1, 2, 3] (by decide +kernel) p40lb)

def p58ws : List ℕ := [0x2aaaaaaaaaaaaaaa8951449522aa4530959095116f7bb2127bde227dfd115ffe2a0000000000000000000000003fff8003fff001fff800fff00, 0x33333333333333331262092644c5ffa929211a22b7bddf7b908844beeeffe2244400000000000fffc0000000003ffffffc000001ffffff00000, 0x3c3c3c3c3c3c3c3c23849238871089c24e7bfc44c7deefbf7dedffc84822844890000000000000000003fff8003ffffffffffffe00000000000, 0x3fc03fc03fc03fc03c0823c0ffe70e0c707ddffffa10f423a10e88d08f44e88f0600000007fff0000003ffffffc000000000000000000000000, 0x3fffc0003fffc0003ff0fc00f7f9eff7ffc1e087041f083c41f10f20f08710f019fffe0007fffffffffc0000000000000000000000000000000, 0x3fffffffc00000003fff3ffff801f007807e00f807e00fc07e01f03f00f81f01e1fffffff800000000000000000000000000000000000000000]
def p58g : ℕ := 0x3fffbfffbfbebb803ffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000
def p58pts := packedSample 6 197 0x30c30c30c30c30c30c30c30c2082082082082082082081861861861861861861861849249249249249249249241041041041041041030c30c30c30c30c30c30c3082082082082082082081c71c71c71c71c71c71c71c61861861861861861861451451451451451451451041041041041041030c30c30c30c30c30c30c2082082082082082041041041041041041000000000000 0x3ceb9e36d74cf2c68922854478d32c6caa9a269648e287ceb9e2879d71b699511289eb6cf289e6da5d651344ae34cb171a6565544d1f2eb6ca2479d7143ce34a278b2aa6871a64e34b289def9e69637d75954cf38d2f6ba79a489e5d650f38ad6d9e592175755444f349d2c9a591c59550e373ae78e285b5d344f2ca272aa68e26964ce2cac6996385955344d2c9a248a1511289
def p58ds : List (ℕ × ℕ) := [(0xf0f0f0f0f0f0f0f <<< 394, 7), (0x5555555555555555 <<< 394, 7), (0xffff0000ffff <<< 394, 6), (0xffff0000ffff0000 <<< 394, 6), (0x3333333333333333 <<< 394, 6), (0x333300003333 <<< 394, 5), (0xffffffff <<< 394, 5)]
theorem p58c0 : PoolLB (0xf0f0f0f0f0f0f0f <<< 394) p58ws p58g 7 :=
  poolFrom (tbl 5 0xfefeeae0) p59lb _ _ _ [0, 1, 5, 2, 3, 4] (fun x => 394 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p58c1 : PoolLB (0x5555555555555555 <<< 394) p58ws p58g 7 :=
  poolFrom (tbl 5 0xfefeeca0) p60lb _ _ _ [5, 0, 1, 2, 3, 4] (fun x => 394 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p58c2 : PoolLB (0xffff0000ffff <<< 394) p58ws p58g 6 :=
  poolFrom (tbl 5 0xfffeee00) p61lb _ _ _ [0, 1, 2, 3, 5, 4] (fun x => 394 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p58c3 : PoolLB (0xffff0000ffff0000 <<< 394) p58ws p58g 6 :=
  poolFrom (tbl 5 0xfffefefa) p62lb _ _ _ [0, 1, 2, 3, 6, 4] (fun x => 410 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p58c4 : PoolLB (0x3333333333333333 <<< 394) p58ws p58g 6 :=
  poolFrom (tbl 5 0xfefeeea0) p42lb _ _ _ [0, 5, 1, 2, 3, 4] (fun x => 394 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p58c5 : PoolLB (0x333300003333 <<< 394) p58ws p58g 5 :=
  poolFrom (tbl 4 0xfea0) p10lb _ _ _ [0, 4, 1, 2, 4, 3] (fun x => 394 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p58c6 : PoolLB (0xffffffff <<< 394) p58ws p58g 5 :=
  poolFrom (tbl 5 0xfefaee00) p64lb _ _ _ [0, 1, 2, 3, 4, 5] (fun x => 394 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def p58hints : PCert := .node 0x40300040003000000000304040301010101010101010101010100050005030404030005000501010101020202020202020202020202010101010201020202020202 [
  .node 0x6000102000005000202000505050000000003040403010101010202020205050500 [
    .node 0x1 [],
    .node 0x600010002000500 [
      .node 0x0 [],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [],
      .node 0x0 [
        .node 0x0 [],
        .node 0x0 []
      ]
    ],
    .node 0x0 [
      .node 0x0 []
    ],
    .node 0x0 [
      .node 0x0 []
    ],
    .node 0x600 [
      .node 0x0 []
    ],
    .node 0x1 [],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x5 [
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x0 [
      .node 0x0 [
        .node 0x0 [],
        .node 0x0 []
      ],
      .node 0x0 []
    ]
  ],
  .node 0x60001020000000501010202050500050000000003040403010101010202020205050500 [
    .node 0x1 [],
    .node 0x6000100020000 [
      .node 0x0 [],
      .node 0x0 [],
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x60005 [
      .node 0x0 []
    ],
    .node 0x1 [],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x5 [
      .node 0x0 []
    ],
    .node 0x5 [],
    .node 0x0 []
  ],
  .node 0x10206000000050001010202070505050304040300000000010101010202020205050507 [
    .node 0x600010002000500 [
      .node 0x0 [],
      .node 0x0 [],
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x0 [],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x5 [
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x5 []
  ],
  .node 0x102060707000005020205050705030606040407000300070007010101010202020205050507 [
    .node 0x0 [
      .node 0x0 []
    ],
    .node 0x5 [],
    .node 0x102020204010304 [],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x5 [
      .node 0x0 []
    ]
  ],
  .node 0x1020202070707070700030700040407000301010101010700010507000700070005020202020207000207070007 [
    .node 0x0 [],
    .node 0x7070707070001000000 [
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 [],
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 []
    ],
    .node 0x1020707070707000202 [
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x10206070202 [],
    .node 0x202070707070202 [],
    .node 0x10202020304 [],
    .node 0x10202020304 [],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 [],
      .node 0x0 []
    ]
  ],
  .node 0x102020200000000020201010000020207000700030404030101010105000000000500000202020200000707 [
    .node 0x1 [],
    .node 0x0 [],
    .node 0x102060005050105020202050005050505 [
      .node 0x6000100 [
        .node 0x0 [],
        .node 0x0 []
      ],
      .node 0x0 [
        .node 0x0 []
      ]
    ],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x0 [
      .node 0x0 []
    ],
    .node 0x10200000202 [
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x5 [],
    .node 0x0 [],
    .node 0x0 [
      .node 0x0 [],
      .node 0x0 [],
      .node 0x0 []
    ],
    .node 0x1 [],
    .node 0x5 [
      .node 0x0 []
    ],
    .node 0x5 [
      .node 0x0 []
    ],
    .node 0x5 [
      .node 0x0 []
    ],
    .node 0x5 [
      .node 0x0 []
    ],
    .node 0x7 [
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 []
    ],
    .node 0x6 [
      .node 0x0 []
    ]
  ],
  .node 0x10202020000010100000202070000070304040301010101050000050202020200000707 [
    .node 0x1 [],
    .node 0x0 [
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x0 [],
    .node 0x1 [],
    .node 0x0 [
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x5 [],
    .node 0x0 [],
    .node 0x0 []
  ],
  .node 0x102020207070700020207000707030700040407000301010101050700050202020207070007 [
    .node 0x0 [
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x1020202020204010304 [],
    .node 0x10202020304 [],
    .node 0x0 [
      .node 0x0 []
    ],
    .node 0x0 []
  ],
  .node 0x10101010005000501010101020202020101010102010202020202020007000701010101010105070005020202020202040404040101040101010404040402020202030303 [
    .node 0x5 [],
    .node 0x70000 [
      .node 0x0 [
        .node 0x0 []
      ],
      .node 0x0 []
    ],
    .node 0x0 [],
    .node 0x0 [
      .node 0x0 [
        .node 0x0 [],
        .node 0x0 []
      ],
      .node 0x0 []
    ],
    .node 0x0 []
  ],
  .node 0x10101010605060501010101020202020101010102010202020202020007000701010101050606050202020203030303010101010303030302020202030403 [
    .node 0x6 [
      .node 0x0 []
    ],
    .node 0x0 []
  ]
]

theorem p58lb : LB (tbl 6 0xfffefffefefaee00) 9 := by
  apply finishPool (tbl 6 0xfffefffefefaee00) p58ws p58g 197 8 p58pts p58ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p58g % (2^197) = 0 ∧ (p58g >>> 197) % (2^197) = 2^197-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p58ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p58c0⟩
    · exact ⟨by decide +kernel, p58c1⟩
    · exact ⟨by decide +kernel, p58c2⟩
    · exact ⟨by decide +kernel, p58c3⟩
    · exact ⟨by decide +kernel, p58c4⟩
    · exact ⟨by decide +kernel, p58c5⟩
    · exact ⟨by decide +kernel, p58c6⟩
  · decide +kernel
  · apply ptop_at_root (by decide +kernel)
    apply certCheck_sound _ _ _ _ _ _ _ _ p58hints
    decide +kernel

theorem p66lb : LB (tbl 5 0xfefeeea8) 7 := 
  pullLB (tbl 5 0xfefeeea8) (tbl 5 0xfffeeae0) [4, 0, 1, 3, 2] (by decide +kernel) p8lb

theorem p67lb : LB (tbl 5 0xfefeee88) 7 := 
  pullLB (tbl 5 0xfefeee88) (tbl 5 0xfffaeea0) [0, 4, 1, 2, 3] (by decide +kernel) p13lb

theorem p68lb : LB (tbl 5 0xfefefee0) 6 := 
  pullLB (tbl 5 0xfefefee0) (tbl 5 0xfffeeee0) [0, 1, 4, 2, 3] (by decide +kernel) p31lb

theorem p69lb : LB (tbl 5 0xfffffeea) 6 := 
  pullLB (tbl 5 0xfffffeea) (tbl 5 0xfffefefa) [0, 1, 3, 4, 2] (by decide +kernel) p62lb

def p65ws : List ℕ := [0xaaaaaaaaaaaaaaaa2544892a454c4aa425a425845c44df7be889bfff13400000000000000000000000000003fffe000fffc00, 0xcccccccccccccccc4989124c899094c8465eff48a8896fbdb7ffc44a2480000000000000000007fff0000003fffffff000000, 0xf0f0f0f0f0f0f0f08e1224710e21271eff68465133fff2113912c89348c000000000000007fff8000000fffc0000000000000, 0xff00ff00ff00ff00f0204781ffc6381f779f77bffd118421c223111c81000000007fff0007ffffffffff00000000000000000, 0xffff0000ffff0000ffc3f801effbfff078107821c21e083e043c21e00e3fffe0007ffffff8000000000000000000000000000, 0xffffffff00000000fffc7ffff003c01f801f803e03e00fc007c03e00f03fffffff80000000000000000000000000000000000]
def p65g : ℕ := 0xfffefffefefeeae0ffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000
def p65pts := packedSample 6 170 0xc30c30c30c30c30c30c30c30c2082082082082082082081861861861861861861861841041041041041041040c30c30c30c30c30c30c30c30a28a28a28a28a28a28a28a2082082082082082081041041041041041041040c30c30c30c30c30c30c30c30c2082082082082082082041041041041041041041000000000000000 0xf3ae78db5d33cb1a248a1512478d32c6caa9a269648e287ceb9e2879d71b699512449e34cb171a6565544d247cbadb2891e75c50f38d24617ababaa889e6da48f38b246e2caa9a1c69938d2c9d2c9a591c59550e347185ceb9e38a16d74d244f2c91c6172aa68e26964d238b1c6c6996385955344d2c91c5a248a1512449185
def p65ds : List (ℕ × ℕ) := [(0xffffffff <<< 340, 7), (0xffff0000ffff <<< 340, 7), (0x3333333333333333 <<< 340, 7), (0x5555555555555555 <<< 340, 7), (0xff00ff00ff00ff <<< 340, 6), (0xff00ff00ff00ff00 <<< 340, 6)]
theorem p65c0 : PoolLB (0xffffffff <<< 340) p65ws p65g 7 :=
  poolFrom (tbl 5 0xfefeeae0) p59lb _ _ _ [0, 1, 2, 3, 4, 5] (fun x => 340 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p65c1 : PoolLB (0xffff0000ffff <<< 340) p65ws p65g 7 :=
  poolFrom (tbl 5 0xfffeeae0) p8lb _ _ _ [0, 1, 2, 3, 5, 4] (fun x => 340 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p65c2 : PoolLB (0x3333333333333333 <<< 340) p65ws p65g 7 :=
  poolFrom (tbl 5 0xfefeeea8) p66lb _ _ _ [0, 5, 1, 2, 3, 4] (fun x => 340 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p65c3 : PoolLB (0x5555555555555555 <<< 340) p65ws p65g 7 :=
  poolFrom (tbl 5 0xfefeee88) p67lb _ _ _ [5, 0, 1, 2, 3, 4] (fun x => 340 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p65c4 : PoolLB (0xff00ff00ff00ff <<< 340) p65ws p65g 6 :=
  poolFrom (tbl 5 0xfefefee0) p68lb _ _ _ [0, 1, 2, 5, 3, 4] (fun x => 340 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p65c5 : PoolLB (0xff00ff00ff00ff00 <<< 340) p65ws p65g 6 :=
  poolFrom (tbl 5 0xfffffeea) p69lb _ _ _ [0, 1, 2, 6, 3, 4] (fun x => 348 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def p65hints : PCert := .node 0x10101010101010101010202020201010101020202020500060600050101010102020202030303030303030301010101020202020404040404040404030303030403 [
  .node 0x1010101010101010101020202020101010102020202030303030403010101010101020202020303030304040404040401010101020202020303030304040404050505 [],
  .node 0x10101010101010101010202020201010101020202020303030304030101010102020202030303030404040401010101020202020303030304040404050605 []
]

theorem p65lb : LB (tbl 6 0xfffefffefefeeae0) 9 := by
  apply finishPool (tbl 6 0xfffefffefefeeae0) p65ws p65g 170 8 p65pts p65ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p65g % (2^170) = 0 ∧ (p65g >>> 170) % (2^170) = 2^170-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p65ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p65c0⟩
    · exact ⟨by decide +kernel, p65c1⟩
    · exact ⟨by decide +kernel, p65c2⟩
    · exact ⟨by decide +kernel, p65c3⟩
    · exact ⟨by decide +kernel, p65c4⟩
    · exact ⟨by decide +kernel, p65c5⟩
  · decide +kernel
  · apply ptop_at_root (by decide +kernel)
    apply certCheck_sound _ _ _ _ _ _ _ _ p65hints
    decide +kernel

theorem p70lb : LB (tbl 6 0xfffefffafefeeea0) 9 := 
  pullLB (tbl 6 0xfffefffafefeeea0) (tbl 6 0xfffefffafefefca0) [2, 1, 0, 3, 4, 5] (by decide +kernel) p48lb

def p71ws : List ℕ := [0xaaaaaaaaaaaaaaaa2549249824b22a4255212beff4458889889ffdd892fffc940000000000000000000007fff0000000000fffe001fff00, 0xcccccccccccccccc4982fed649244ca4a6423442588afddf112bdef7ff8898280003fff800000000000000000000fffe000ffffffe00000, 0xf0f0f0f0f0f0f0f08e1448e091c8710938f7fa8465133fedfffc889924912d44000000000000000003fff8000000fffffff000000000000, 0xff00ff00ff00ff00f0208f031e0ffe31c0fbbdf77bffd10e223110e24722320800000000003fff8003ffffffffff0000000000000000000, 0xffff0000ffff0000ffc7f005e00f7fdfff83c107821c21f043c21f047843c073fffc0000003ffffffc00000000000000000000000000000, 0xffffffff00000000fff8fff9ffff801e00fc01f803e03e007c03e007807c0383ffffffffffc000000000000000000000000000000000000]
def p71g : ℕ := 0xfffefffafefeeca0fffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000000000
def p71pts := packedSample 6 190 0xc30c30c30c30c30c30c30c308a28a28a28a28a28a28a28a082082082082082082061861861861861861861861041041041041041041030c30c30c30c30c30c30c3092492492492492492492492082082082082082081861861861861861861861841041041041041041040c30c30c30c30c30c30c30c2082082082082082081041041041041041041000000000000 0xf3ae78db5d33cb1a24854491eb6cf2babaa89e69238522b8d32c6caa9a269648e1f3ae78a1e75c6da6544912b8d32c5c699595513491f2eb6ca2479d7143ce34a179b6ba6885d6d944f34b285e2caa9a1c69938d2cadae9e691e5d65123ce287174b2696471655438d1c5ceb9e385b5d34913cb287172aa68da59348e2ca1f1a658e16554d134b1c5a24854491285
def p71ds : List (ℕ × ℕ) := [(0xffffffff <<< 380, 7), (0xffff0000ffff <<< 380, 7), (0xff00ff00ff00ff <<< 380, 7), (0xf0f0f0f0f0f0f0f <<< 380, 7), (0x3333333333333333 <<< 380, 7)]
theorem p71c0 : PoolLB (0xffffffff <<< 380) p71ws p71g 7 :=
  poolFrom (tbl 5 0xfefeeca0) p60lb _ _ _ [0, 1, 2, 3, 4, 5] (fun x => 380 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p71c1 : PoolLB (0xffff0000ffff <<< 380) p71ws p71g 7 :=
  poolFrom (tbl 5 0xfffaeca0) p15lb _ _ _ [0, 1, 2, 3, 5, 4] (fun x => 380 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p71c2 : PoolLB (0xff00ff00ff00ff <<< 380) p71ws p71g 7 :=
  poolFrom (tbl 5 0xfefafea0) p50lb _ _ _ [0, 1, 2, 5, 3, 4] (fun x => 380 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p71c3 : PoolLB (0xf0f0f0f0f0f0f0f <<< 380) p71ws p71g 7 :=
  poolFrom (tbl 5 0xfefaeec0) p34lb _ _ _ [0, 1, 5, 2, 3, 4] (fun x => 380 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p71c4 : PoolLB (0x3333333333333333 <<< 380) p71ws p71g 7 :=
  poolFrom (tbl 5 0xfefeee88) p67lb _ _ _ [0, 5, 1, 2, 3, 4] (fun x => 380 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem p71lb : LB (tbl 6 0xfffefffafefeeca0) 9 := by
  apply finishPool (tbl 6 0xfffefffafefeeca0) p71ws p71g 190 8 p71pts p71ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p71g % (2^190) = 0 ∧ (p71g >>> 190) % (2^190) = 2^190-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p71ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p71c0⟩
    · exact ⟨by decide +kernel, p71c1⟩
    · exact ⟨by decide +kernel, p71c2⟩
    · exact ⟨by decide +kernel, p71c3⟩
    · exact ⟨by decide +kernel, p71c4⟩
  · decide +kernel
  · decide +kernel

def p57ws : List ℕ := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa112a22222540889a212a2844951045544114c10958842542116fbef7621093ff7bc2227efbfa108affffc454000000000000000000000000000000000000000000000000001fffff80000fffff0000fffff80003ffff000, 0xcccccccccccccccccccccccccccccccc224c44444681112c424c40892620898beffea2129108468422b7df7bbffbdc42110444bf7dddffff084488880000000000000000000000000000000fffff800000000000001ffffffffff000000000fffffffffc0000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0447009ff773222308470911238410e2082270424e7deff0844c7efbddf7dfbefbdbfffc41090211410890120000007ffffc000000000000000000000000000001fffff00001fffffffffffffffffff00000000000000000, 0xff00ff00ff00ff00ff00ff00ff00ff0087809088780443c107810223c0fbffcd0438284707ff77fffff90421e4211c8421c888c8211e42272111d20c00000000000000000000000003fffff0000000001fffffffffe000000000000000000000000000000000000, 0xffff0000ffff0000ffff0000ffff0000f801010f80187c01fffe1c3c00fdeff3f7bfdffffa1078108702083e0841e1083e110f1041e08438421e20300000000000000007ffffe00003ffffffffffffffe0000000000000000000000000000000000000000000000, 0xffffffff00000000ffffffff00000000fffe1ff0002f8001f7ffe7ffff81f00207c01078041f8020f8040fc0107e020fc021f0207e0107c083e003c3fffff80000000007fffffffffc0000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffff0000000000000000ffffe1ffffcffffff80007c000fe0003f8001f8007e0003f0007f0001f8003f0003e003f8001f800fc003c03fffffffffffffff800000000000000000000000000000000000000000000000000000000000000000000000]
def p57g : ℕ := 0xfffffffeffffffeefffefffefefaee00fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def p57pts := packedSample 7 350 0x3060c183060c183060c183060c183060c183060c11224489122448912244891224489122448912040810204081020408102040810204080c183060c183060c183060c183060c183060c182040810204081020408102040810204080c183060c183060c183060c183060c183060c18244891224489122448912244891224489122440810204081020408102040810204080c183060c183060c183060c183060c183060c102040810204081020408102040810204070e1c3870e1c3870e1c3870e1c3870e1c3870e183060c183060c183060c183060c183060a142850a142850a142850a142850a142850810204081020408102040810204060c183060c183060c183060c183060c183060810204081020408102040810204080810204081020408102040810204081000000000000000000000 0x3c74e5c786cd5a7466cb931e2c34244282a122243d3666cb92e56ab5284e9b324478d161414853868c98b0d8a94a8d0992a4c88d161c283e3a72e3c283c74e5c366ad19b262a122242508f0d19316170d193158a94a84c952234487c5cb566c5090f1d3970a0f1d386cd192844509e56ab53a54213a6ccd9223c6cd172c5099115c2c54a54683868c989c3464b15284c8ecb93a6cc90f172d58a121e3a70a0f1c34509d16264a9321c2c54a541c346470d16284e7af3e3c68b0dbaf4e992a33e5cb15263c70d179ab4e8f1a1365c9d3244478b96283c70acb566c78b05aad4e952213a5ca94223c689c9526468ad16264a90e162a5070dc74e5c7870a0b3569d1a2426cb93223c58a138a94a8d0e13254991a2345898e162b0d193161c162a52a34264a932234589a12214150911212844509
def p57ds : List (ℕ × ℕ) := [(0xffffffffffffffff <<< 700, 9), (0xffffffff00000000ffffffff <<< 700, 9), (0xff00ff00ff00ff00ff00ff00ff00ff <<< 700, 9), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f <<< 700, 9), (0x33333333333333333333333333333333 <<< 700, 9), (0x55555555555555555555555555555555 <<< 700, 9)]
theorem p57c0 : PoolLB (0xffffffffffffffff <<< 700) p57ws p57g 9 :=
  poolFrom (tbl 6 0xfffefffefefaee00) p58lb _ _ _ [0, 1, 2, 3, 4, 5, 6] (fun x => 700 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16 + (x 5).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p57c1 : PoolLB (0xffffffff00000000ffffffff <<< 700) p57ws p57g 9 :=
  poolFrom (tbl 6 0xffffffeefefaee00) p7lb _ _ _ [0, 1, 2, 3, 4, 6, 5] (fun x => 700 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p57c2 : PoolLB (0xff00ff00ff00ff00ff00ff00ff00ff <<< 700) p57ws p57g 9 :=
  poolFrom (tbl 6 0xfffeffeefefefa00) p33lb _ _ _ [0, 1, 2, 6, 3, 4, 5] (fun x => 700 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p57c3 : PoolLB (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f <<< 700) p57ws p57g 9 :=
  poolFrom (tbl 6 0xfffefffefefeeae0) p65lb _ _ _ [0, 1, 6, 2, 3, 4, 5] (fun x => 700 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p57c4 : PoolLB (0x33333333333333333333333333333333 <<< 700) p57ws p57g 9 :=
  poolFrom (tbl 6 0xfffefffafefeeea0) p70lb _ _ _ [0, 6, 1, 2, 3, 4, 5] (fun x => 700 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p57c5 : PoolLB (0x55555555555555555555555555555555 <<< 700) p57ws p57g 9 :=
  poolFrom (tbl 6 0xfffefffafefeeca0) p71lb _ _ _ [6, 0, 1, 2, 3, 4, 5] (fun x => 700 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def p57hints : PCert := .node 0x1010101010101010202020201010101020202020303030301010101020202020404040403030303010101010202020205050505030303030404040401010101020202020606060603030303040404040604050505050605 []

theorem p57lb : LB (tbl 7 0xfffffffeffffffeefffefffefefaee00) 11 := by
  apply finishPool (tbl 7 0xfffffffeffffffeefffefffefefaee00) p57ws p57g 350 10 p57pts p57ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p57g % (2^350) = 0 ∧ (p57g >>> 350) % (2^350) = 2^350-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p57ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p57c0⟩
    · exact ⟨by decide +kernel, p57c1⟩
    · exact ⟨by decide +kernel, p57c2⟩
    · exact ⟨by decide +kernel, p57c3⟩
    · exact ⟨by decide +kernel, p57c4⟩
    · exact ⟨by decide +kernel, p57c5⟩
  · decide +kernel
  · apply ptop_at_root (by decide +kernel)
    apply certCheck_sound _ _ _ _ _ _ _ _ p57hints
    decide +kernel

theorem p73lb : LB (tbl 6 0xfffefffefefaeee0) 9 := 
  pullLB (tbl 6 0xfffefffefefaeee0) (tbl 6 0xfffefffefefeeae0) [0, 1, 5, 4, 3, 2] (by decide +kernel) p65lb

theorem p74lb : LB (tbl 6 0xfffefffefefeeea8) 9 := 
  pullLB (tbl 6 0xfffefffefefeeea8) (tbl 6 0xfffffffefefaeee0) [5, 0, 1, 4, 3, 2] (by decide +kernel) p19lb

theorem p75lb : LB (tbl 6 0xfffefffefefeeca8) 9 := 
  pullLB (tbl 6 0xfffefffefefeeca8) (tbl 6 0xfffefffefefeeae0) [2, 0, 1, 3, 4, 5] (by decide +kernel) p65lb

def p72ws : List ℕ := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa112a1108895109514224a8822aa208a6042562084aa108b421137efbfb421157ffff845500000000000000000000000000000000000000000000000000003fffffc00007ffff8000, 0xcccccccccccccccccccccccccccccccc224c221112621262044931044c5f7ff5884a44108d4211584225bf7dddbffff84225088a000000000000000000000000001fffff800000000000000000003ffffffffff800000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f044704422238423848891c2087104113890939f7dfe642263ffffc41091c42298844991230000000000000000000000000000000000001fffffe00003ffffc0000000000000000000, 0xff00ff00ff00ff00ff00ff00ff00ff00878088443c083c08111e07dffe6821c1211c1fbeef9ffffc844608211e0844e1088e220c0000000000000000000007ffffe0000000001ffffffffffc000000000000000000000000, 0xffff0000ffff0000ffff0000ffff0000f8010087c00ffff0e1e007ef7f9fbdfe7fffe820f008438108781041e010870210f0403000000000000fffffc00007ffffffffffffffe00000000000000000000000000000000000, 0xffffffff00000000ffffffff00000000fffe0ff8000fbfff3ffffc0f80103e0041e0103f00107c020f80207e0020f8041f0003c0ffffff00000ffffffffff800000000000000000000000000000000000000000000000000, 0xffffffffffffffff0000000000000000fffff0ffffffc0003e0007f0001fc0007e001fc0001f8003f0003f80003f0007e0007c00fffffffffff0000000000000000000000000000000000000000000000000000000000000]
def p72g : ℕ := 0xfffffffefffffffefffefffefefaeee0ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000
def p72pts := packedSample 7 288 0xc183060c183060c183060c183060c183060c1830608102040810204081020408102040810204060c183060c183060c183060c183060c183060c102040810204081020408102040810204060c183060c183060c183060c183060c183060c12244891224489122448912244891224489122440810204081020408102040810204080c183060c183060c183060c183060c183060c18306081020408102040810204081020408102020408102040810204081020408102040810183060c183060c183060c183060c183060c183060c1020408102040810204081020408102040408102040810204081020408102040810200000000000000000000000000 0xf1d3971e1b3569d19b2e4c78b0d091121415091121e1a3262c362a52a34264a9322345890e141f1d3971e141e3a72e1b3568cd93150911212847868c98b0b868c98ac54a54264a911a243e2e5ab36284878e9cb85078e9c3668c9422284f2b55a9d2a109d3666c911e3668b96284c88a0dc2c54a54683868c989c3464b15284c8ecb93a6cc9111e2e5ab14243c74e141e3868a12182e8b13254990e162a52a0e1a323868b1427254991a2c468b13254870b1528386870c171d3971e1c282cd5a7468909b2e4c88f16284870c17152951a1c264a93234468b131c2c5070d868c98b0e0b152951a132549911a2c4870b4244485054244484a111424305
def p72ds : List (ℕ × ℕ) := [(0xffffffffffffffff <<< 576, 9), (0xffffffff00000000ffffffff <<< 576, 9), (0xff00ff00ff00ff00ff00ff00ff00ff <<< 576, 9), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f <<< 576, 9), (0x33333333333333333333333333333333 <<< 576, 9), (0x55555555555555555555555555555555 <<< 576, 9)]
theorem p72c0 : PoolLB (0xffffffffffffffff <<< 576) p72ws p72g 9 :=
  poolFrom (tbl 6 0xfffefffefefaeee0) p73lb _ _ _ [0, 1, 2, 3, 4, 5, 6] (fun x => 576 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16 + (x 5).toNat * 32) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p72c1 : PoolLB (0xffffffff00000000ffffffff <<< 576) p72ws p72g 9 :=
  poolFrom (tbl 6 0xfffffffefefaeee0) p19lb _ _ _ [0, 1, 2, 3, 4, 6, 5] (fun x => 576 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p72c2 : PoolLB (0xff00ff00ff00ff00ff00ff00ff00ff <<< 576) p72ws p72g 9 :=
  poolFrom (tbl 6 0xfffefffefefefae0) p45lb _ _ _ [0, 1, 2, 6, 3, 4, 5] (fun x => 576 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p72c3 : PoolLB (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f <<< 576) p72ws p72g 9 :=
  poolFrom (tbl 6 0xfffefffefefeeae0) p65lb _ _ _ [0, 1, 6, 2, 3, 4, 5] (fun x => 576 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p72c4 : PoolLB (0x33333333333333333333333333333333 <<< 576) p72ws p72g 9 :=
  poolFrom (tbl 6 0xfffefffefefeeea8) p74lb _ _ _ [0, 6, 1, 2, 3, 4, 5] (fun x => 576 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p72c5 : PoolLB (0x55555555555555555555555555555555 <<< 576) p72ws p72g 9 :=
  poolFrom (tbl 6 0xfffefffefefeeca8) p75lb _ _ _ [6, 0, 1, 2, 3, 4, 5] (fun x => 576 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def p72hints : PCert := .node 0x10101010101010101010202020201010101020202020303030301010101020202020404040403030303040301010101020202020505050503030303040404040101010102020202060606060303030304040404050505050605 []

theorem p72lb : LB (tbl 7 0xfffffffefffffffefffefffefefaeee0) 11 := by
  apply finishPool (tbl 7 0xfffffffefffffffefffefffefefaeee0) p72ws p72g 288 10 p72pts p72ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p72g % (2^288) = 0 ∧ (p72g >>> 288) % (2^288) = 2^288-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p72ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p72c0⟩
    · exact ⟨by decide +kernel, p72c1⟩
    · exact ⟨by decide +kernel, p72c2⟩
    · exact ⟨by decide +kernel, p72c3⟩
    · exact ⟨by decide +kernel, p72c4⟩
    · exact ⟨by decide +kernel, p72c5⟩
  · decide +kernel
  · apply ptop_at_root (by decide +kernel)
    apply certCheck_sound _ _ _ _ _ _ _ _ p72hints
    decide +kernel

theorem p76lb : LB (tbl 7 0xfffffffefffffffafffefffefefeaaa0) 11 := 
  pullLB (tbl 7 0xfffffffefffffffafffefffefefeaaa0) (tbl 7 0xfffffffeffffffeefffefffefffaee00) [3, 2, 0, 1, 4, 5, 6] (by decide +kernel) p32lb

theorem p77lb : LB (tbl 7 0xfffffffefffffffafffefffefefcaaa0) 11 := 
  pullLB (tbl 7 0xfffffffefffffffafffefffefefcaaa0) (tbl 7 0xfffffffeffffffeefffefffefefaee00) [3, 2, 0, 1, 4, 5, 6] (by decide +kernel) p57lb

theorem p79lb : LB (tbl 6 0xfffefffefefcaaa0) 9 := 
  pullLB (tbl 6 0xfffefffefefcaaa0) (tbl 6 0xfffefffefefaee00) [3, 2, 0, 1, 4, 5] (by decide +kernel) p58lb

theorem p78lb : LB (tbl 7 0xfffffffefffffffefffefffaeeeeee00) 10 := 
  rule1 (tbl 7 0xfffffffefffffffefffefffaeeeeee00) 0 false 9 8 0 10 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 7 0xfffffffefffffffefffefffaeeeeee00) 0 false) (tbl 6 0xfffefffefefcaaa0) [6, 0, 1, 2, 3, 4, 5] (by decide +kernel) p79lb)

theorem p81lb : LB (tbl 6 0xfffefffafffeaaa0) 8 := 
  pullLB (tbl 6 0xfffefffafffeaaa0) (tbl 6 0xfffeffeefffeee00) [3, 2, 0, 1, 4, 5] (by decide +kernel) p56lb

theorem p80lb : LB (tbl 7 0xfffffffeffffffeefffffffeeeeeee00) 9 := 
  rule1 (tbl 7 0xfffffffeffffffeefffffffeeeeeee00) 0 false 8 8 0 10 (by decide +kernel) (by decide +kernel) (pullLB (rs (tbl 7 0xfffffffeffffffeefffffffeeeeeee00) 0 false) (tbl 6 0xfffefffafffeaaa0) [6, 0, 1, 2, 3, 4, 5] (by decide +kernel) p81lb)

def p1ws : List ℕ := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa041082104110842210fc1f3e1f0000000000000000007c1f3e1f, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc08210420bf010844217fe03fe0000000003f000000007fe03fe0, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f013f00841022f83e1f07fffc00003f00000000f83e1f07fffc000, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0020421082044ffc01ff8421022100000000000ffc01ff80000000, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff00004084210fc80ffffe00084204420000000fc00ffffe0000000000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff0000000081087e0ffff21080421084480400007e0ffff000000000000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000fe007ff4100421088421089088fc007ff0000000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffc008208842110842102110ffff8000000000000000000000]
def p1g : ℕ := 0xfffffffffffffffeffffffffffffffeefffffffefffffffefffefffaeeeeee00ffffffffffffffffffffffffff00000000000000000000000000
def p1pts := packedSample 8 104 0xc0c0c0c0c0c084848484848480808080806060606060604040404040303030303030222222222222202020201c1c1c1c1c18181818181414141414101010100c0c0c0c0c080808080807070707070606060606050505050504040303030303020202020101010101 0xe0d0c8c4c2c1c4a4948c8685a090888281e070686462615048444241b07038343231a262322a2623a02824219c5c3c1e1d9858381a199454341615905012118c4c2c0e0d8848280a09874727170f864626160e854525150d4424834323130b8242120a8141211109
def p1ds : List (ℕ × ℕ) := [(0xffffffffffffffff0000000000000000ffffffffffffffff <<< 208, 11), (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff <<< 208, 11), (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff <<< 208, 11), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f <<< 208, 11), (0x3333333333333333333333333333333333333333333333333333333333333333 <<< 208, 11), (0x5555555555555555555555555555555555555555555555555555555555555555 <<< 208, 11), (0xffffffffffffffffffffffffffffffff <<< 208, 10), (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff <<< 208, 9)]
theorem p1c0 : PoolLB (0xffffffffffffffff0000000000000000ffffffffffffffff <<< 208) p1ws p1g 11 :=
  poolFrom (tbl 7 0xffffffffffffffeefffefffaeeeeee00) p2lb _ _ _ [0, 1, 2, 3, 4, 5, 7, 6] (fun x => 208 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16 + (x 5).toNat * 32 + (x 6).toNat * 128) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p1c1 : PoolLB (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff <<< 208) p1ws p1g 11 :=
  poolFrom (tbl 7 0xfffffffeffffffeefffefffefffaee00) p32lb _ _ _ [0, 1, 2, 3, 7, 4, 5, 6] (fun x => 208 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 32 + (x 5).toNat * 64 + (x 6).toNat * 128) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p1c2 : PoolLB (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff <<< 208) p1ws p1g 11 :=
  poolFrom (tbl 7 0xfffffffeffffffeefffefffefefaee00) p57lb _ _ _ [0, 1, 2, 7, 3, 4, 5, 6] (fun x => 208 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64 + (x 6).toNat * 128) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p1c3 : PoolLB (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f <<< 208) p1ws p1g 11 :=
  poolFrom (tbl 7 0xfffffffefffffffefffefffefefaeee0) p72lb _ _ _ [0, 1, 7, 2, 3, 4, 5, 6] (fun x => 208 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64 + (x 6).toNat * 128) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p1c4 : PoolLB (0x3333333333333333333333333333333333333333333333333333333333333333 <<< 208) p1ws p1g 11 :=
  poolFrom (tbl 7 0xfffffffefffffffafffefffefefeaaa0) p76lb _ _ _ [0, 7, 1, 2, 3, 4, 5, 6] (fun x => 208 + (x 0).toNat * 1 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64 + (x 6).toNat * 128) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p1c5 : PoolLB (0x5555555555555555555555555555555555555555555555555555555555555555 <<< 208) p1ws p1g 11 :=
  poolFrom (tbl 7 0xfffffffefffffffafffefffefefcaaa0) p77lb _ _ _ [7, 0, 1, 2, 3, 4, 5, 6] (fun x => 208 + (x 0).toNat * 2 + (x 1).toNat * 4 + (x 2).toNat * 8 + (x 3).toNat * 16 + (x 4).toNat * 32 + (x 5).toNat * 64 + (x 6).toNat * 128) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p1c6 : PoolLB (0xffffffffffffffffffffffffffffffff <<< 208) p1ws p1g 10 :=
  poolFrom (tbl 7 0xfffffffefffffffefffefffaeeeeee00) p78lb _ _ _ [0, 1, 2, 3, 4, 5, 6, 7] (fun x => 208 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16 + (x 5).toNat * 32 + (x 6).toNat * 64) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem p1c7 : PoolLB (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff <<< 208) p1ws p1g 9 :=
  poolFrom (tbl 7 0xfffffffeffffffeefffffffeeeeeee00) p80lb _ _ _ [0, 1, 2, 3, 4, 7, 5, 6] (fun x => 208 + (x 0).toNat * 1 + (x 1).toNat * 2 + (x 2).toNat * 4 + (x 3).toNat * 8 + (x 4).toNat * 16 + (x 5).toNat * 64 + (x 6).toNat * 128) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def p1hints : PCert := .node 0x10101010700000701010101020202020101010102020202030303030101010103030303020202020302040404040101010104040404020202020303030303030505050501010101050505050202020203030303040404040606060601010101060606060202020203030303040404040604050505050605 [
  .node 0x10101010101010102020202030201010101020202020303030303030101010102020202030303030404040401010101020202020303030304040404060405050505060501010101020202020303030303030404040404040505050506060606060601010101020202020202030303030303040404040505050505050606060606060707070807070707010101010101010102020202020202020303030303030303040404040404040405050505050505050606060606060606070708070707 [],
  .node 0x101010101010101020202020302010101010202020203030303030301010101020202020303030304040404010101010202020203030303040404040604050505050605010101010101020202020303030304040404050505050606060601010101020202020202030303030303040404040505050505050606060606060707070707080707010101010101010102020202020202020303030303030303040404040404040405050505050505050606060606060606070708070707 []
]

theorem p1lb : LB (tbl 8 0xfffffffffffffffeffffffffffffffeefffffffefffffffefffefffaeeeeee00) 13 := by
  apply finishPool (tbl 8 0xfffffffffffffffeffffffffffffffeefffffffefffffffefffefffaeeeeee00) p1ws p1g 104 12 p1pts p1ds
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i hi
    unfold differs
    have hb : p1g % (2^104) = 0 ∧ (p1g >>> 104) % (2^104) = 2^104-1 := by decide +kernel
    exact pbits _ _ _ hi hb
  · intro t ht
    simp only [p1ds, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide +kernel, p1c0⟩
    · exact ⟨by decide +kernel, p1c1⟩
    · exact ⟨by decide +kernel, p1c2⟩
    · exact ⟨by decide +kernel, p1c3⟩
    · exact ⟨by decide +kernel, p1c4⟩
    · exact ⟨by decide +kernel, p1c5⟩
    · exact ⟨by decide +kernel, p1c6⟩
    · exact ⟨by decide +kernel, p1c7⟩
  · decide +kernel
  · apply ptop_at_root (by decide +kernel)
    apply certCheck_sound _ _ _ _ _ _ _ _ p1hints
    decide +kernel
def Fq : BF 8 := fun x => (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)

theorem binaryBound : LB Fq 13 :=
  pullLB Fq (tbl 8 0xfffffffffffffffeffffffffffffffeefffffffefffffffefffefffaeeeeee00) [0, 1, 2, 3, 4, 5, 6, 7] (by decide +kernel) p1lb
theorem bridge : ∀ x : Fin 8 → Bool, decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) = Fq x := by decide +kernel

def wg : List Gate := [⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [5, 17]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [19, 20]⟩]
theorem wfits : ∀ g ∈ wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wok : ∀ x : Fin 8 → Bool, Circuit.eval ⟨wg, 21⟩ (List.ofFn x) = Fq x := by decide +kernel

theorem short {gates : List Gate} (h : ∃ g ∈ gates, g.op = GateOp.not) : bc gates < gates.length := by
  obtain ⟨g, mem, op⟩ := h
  exact (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, mem, by simp [isBinary, op]⟩


end PEqualNP.Outside.L_meta_31481

theorem PEqualNP.Outside.L_meta_31481 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · have h1 := PEqualNP.Outside.L_meta_31481.short hasNot
    have hb := PEqualNP.Outside.L_meta_31481.bound_of_LB PEqualNP.Outside.L_meta_31481.Fq 13 PEqualNP.Outside.L_meta_31481.binaryBound gates o
      (fun g hg => fits g hg) (fun x => (computes x).trans (PEqualNP.Outside.L_meta_31481.bridge x))
    have hl : PEqualNP.Outside.L_meta_31481.wg.length = 14 := rfl
    exact ⟨PEqualNP.Outside.L_meta_31481.wg, 21, PEqualNP.Outside.L_meta_31481.wfits, by omega,
      fun x => (PEqualNP.Outside.L_meta_31481.wok x).trans (PEqualNP.Outside.L_meta_31481.bridge x).symm⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
