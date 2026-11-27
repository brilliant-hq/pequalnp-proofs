import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25624_aux

def mix (x : ℤ → Bool) (z : ℤ) : Bool := xor (xor (x (z-1)) (x z)) (x (z+1))

def step (x injection : ℤ → Bool) (z : ℤ) : Bool :=
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (injection z)

def block (w : ℕ) (tape : ℤ → Bool) (edge : ℤ) : ℕ :=
  (List.range w).foldl (fun (code j : ℕ) => code ||| ((tape (edge+1+(j : ℤ))).toNat <<< j)) 0

def actual (inj : ℕ → ℤ → Bool) (first : ℕ → ℤ → Bool) (seed time : ℕ) : ℤ → Bool :=
  (List.range time).foldl (fun state tick => step state (inj (tick+1))) (first seed)

def evo (inj : ℕ → ℤ → Bool) (x : ℤ → Bool) (c : ℤ) (t : ℕ) : (ℤ → Bool) × ℤ :=
  (List.range t).foldl (fun (prev : (ℤ → Bool) × ℤ) j =>
      (step prev.1 (inj (j+1)), prev.2-3+((mix prev.1 (prev.2-1)).toNat : ℤ))) (x, c)

def sample (f : ℤ) (ref : ℤ → Bool) (pattern : ℕ) : ℤ → Bool :=
  fun site => if site ≤ f then ref site else pattern.testBit (site-f-1).toNat

def observe (inj : ℕ → ℤ → Bool) (f : ℤ) (ref : ℤ → Bool) (width pattern : ℕ)
    (query : ℕ × ℤ × Bool) : Option Bool :=
  let pair := evo inj (sample f ref pattern) (f + (width : ℤ)) query.1
  if query.2.1 ≤ pair.2 then some (pair.1 query.2.1 == query.2.2) else none

def T (inj : ℕ → ℤ → Bool) (first : ℕ → ℤ → Bool) (tests : List (ℕ × ℤ × Bool)) (key : ℕ) : Bool :=
  tests.all (fun wanted => actual inj first key wanted.1 wanted.2.1 == wanted.2.2)

def body (inj : ℕ → ℤ → Bool) (f : ℤ) (ref : ℤ → Bool) (tests : List (ℕ × ℤ × Bool))
    (mass : ℕ → ℕ → ℕ) (depth : ℕ) (acc : ℕ × List ℕ) (label : ℕ) : ℕ × List ℕ :=
  let weight := mass depth label
  if weight = 0 then acc else
    let answers := tests.map (observe inj f ref depth label)
    if answers.contains (some false) then acc
    else if answers.all (fun answer => answer == some true) then (acc.1+weight, acc.2)
    else (acc.1, label :: (label + 2^depth) :: acc.2)

def outer (inj : ℕ → ℤ → Bool) (f : ℤ) (ref : ℤ → Bool) (tests : List (ℕ × ℤ × Bool))
    (mass : ℕ → ℕ → ℕ) (layer : ℕ × List ℕ) (depth : ℕ) : ℕ × List ℕ :=
  layer.2.foldl (body inj f ref tests mass depth) (layer.1, [])

def G (inj : ℕ → ℤ → Bool) (f : ℤ) (first : ℕ → ℤ → Bool) (tests : List (ℕ × ℤ × Bool))
    (seeds : List ℕ) (d p : ℕ) : ℕ :=
  (seeds.filter (fun k => (block d (first k) f == p) && T inj first tests k)).length

def S (inj : ℕ → ℤ → Bool) (f : ℤ) (first : ℕ → ℤ → Bool) (tests : List (ℕ × ℤ × Bool))
    (seeds : List ℕ) (d : ℕ) (L : List ℕ) : ℕ :=
  (L.map (G inj f first tests seeds d)).sum

theorem step_local (x y inj : ℤ → Bool) (c : ℤ) (h : ∀ z ≤ c, x z = y z) :
    ∀ z ≤ c - 3 + ((mix x (c-1)).toNat : ℤ), step x inj z = step y inj z := by
  intro z hz
  have mixeq : ∀ z, z + 1 ≤ c → mix x z = mix y z := by
    intro z hz; unfold mix; rw [h (z-1) (by omega), h z (by omega), h (z+1) (by omega)]
  by_cases hz3 : z ≤ c - 3
  · unfold step; rw [mixeq z (by omega), mixeq (z+1) (by omega), mixeq (z+2) (by omega)]
  · rcases hmx : mix x (c-1) with _ | _
    · rw [hmx] at hz; simp at hz; omega
    · rw [hmx] at hz; simp at hz
      unfold step
      rw [mixeq z (by omega)]
      have e1 : mix x (z+1) = true := by rw [show z+1 = c-1 by omega]; exact hmx
      have e2 : mix y (z+1) = true := by rw [← mixeq (z+1) (by omega)]; exact e1
      simp [e1, e2]

theorem evo_correct (inj : ℕ → ℤ → Bool) (x y : ℤ → Bool) (c : ℤ) (h : ∀ z ≤ c, x z = y z)
    (t : ℕ) :
    (∀ z ≤ (evo inj x c t).2, (evo inj x c t).1 z =
      ((List.range t).foldl (fun state tick => step state (inj (tick+1))) y) z) ∧
    c - 3 * (t:ℤ) ≤ (evo inj x c t).2 := by
  induction t with
  | zero =>
    simp only [evo, List.range_zero, List.foldl_nil]
    exact ⟨h, by simp⟩
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e : evo inj x c (t+1) = (step (evo inj x c t).1 (inj (t+1)),
        (evo inj x c t).2 - 3 + ((mix (evo inj x c t).1 ((evo inj x c t).2-1)).toNat : ℤ)) := by
      simp only [evo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨step_local _ _ _ _ ih1, ?_⟩
    simp only
    push_cast
    omega

theorem block_succ (d : ℕ) (tape : ℤ → Bool) (e : ℤ) :
    block (d+1) tape e = block d tape e ||| ((tape (e+1+(d:ℤ))).toNat <<< d) := by
  simp only [block, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem block_lt (tape : ℤ → Bool) (e : ℤ) : ∀ d, block d tape e < 2^d := by
  intro d
  induction d with
  | zero => simp [block]
  | succ d ih =>
    rw [block_succ, Nat.shiftLeft_eq, Nat.lor_comm, mul_comm, ← Nat.two_pow_add_eq_or_of_lt ih]
    rw [pow_succ]
    cases tape (e+1+(d:ℤ)) <;> simp <;> omega

theorem block_add (tape : ℤ → Bool) (e : ℤ) (d : ℕ) :
    block (d+1) tape e = block d tape e + (tape (e+1+(d:ℤ))).toNat * 2^d := by
  rw [block_succ, Nat.shiftLeft_eq, Nat.lor_comm, mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt (block_lt tape e d)]
  ring

theorem block_testBit (tape : ℤ → Bool) (e : ℤ) :
    ∀ d j, j < d → (block d tape e).testBit j = tape (e+1+(j:ℤ)) := by
  intro d
  induction d with
  | zero => intro j hj; omega
  | succ d ih =>
    intro j hj
    rw [block_succ, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases Nat.lt_or_ge j d with h | h
    · rw [ih j h]
      have : ¬ (j ≥ d) := by omega
      simp [this]
    · have : j = d := by omega
      subst this
      rw [Nat.testBit_lt_two_pow (block_lt tape e j)]
      cases tape (e+1+(j:ℤ)) <;> simp

theorem sample_agree (f : ℤ) (ref : ℤ → Bool) (first : ℤ → Bool) (d p : ℕ)
    (h1 : ∀ z ≤ f, first z = ref z) (hb : block d first f = p) :
    ∀ z ≤ f + (d:ℤ), sample f ref p z = first z := by
  intro z hz
  unfold sample
  split_ifs with h
  · exact (h1 z h).symm
  · have hj : (z - f - 1).toNat < d := by omega
    rw [← hb, block_testBit first f d _ hj]
    congr 1
    omega

theorem observe_correct (inj : ℕ → ℤ → Bool) (f : ℤ) (ref : ℤ → Bool) (first : ℕ → ℤ → Bool)
    (k d p : ℕ) (h1 : ∀ z ≤ f, first k z = ref z) (hb : block d (first k) f = p)
    (q : ℕ × ℤ × Bool) (v : Bool) (hq : observe inj f ref d p q = some v) :
    (actual inj first k q.1 q.2.1 == q.2.2) = v := by
  unfold observe at hq
  have H := (evo_correct inj (sample f ref p) (first k) (f + d)
    (sample_agree f ref (first k) d p h1 hb) q.1).1
  simp only at hq
  split_ifs at hq with hz
  simp only [Option.some.injEq] at hq
  rw [← hq, H _ hz]
  rfl

theorem observe_some (inj : ℕ → ℤ → Bool) (f : ℤ) (ref : ℤ → Bool) (d p : ℕ)
    (q : ℕ × ℤ × Bool) (hq : q.2.1 + 3*(q.1:ℤ) ≤ f + d) : observe inj f ref d p q ≠ none := by
  unfold observe
  have H2 := (evo_correct inj (sample f ref p) (sample f ref p) (f+d) (fun _ _ => rfl) q.1).2
  simp only
  rw [if_pos (by omega)]
  simp

theorem len_mono {α : Type} (q r : α → Bool) : ∀ l : List α,
    (∀ k ∈ l, q k = true → r k = true) → (l.filter q).length ≤ (l.filter r).length
  | [], _ => by simp
  | a :: l, h => by
    have ih := len_mono q r l (fun k hk => h k (by simp [hk]))
    have ha := h a (by simp)
    cases hq : q a <;> cases hr : r a <;> simp [List.filter_cons, hq, hr] at ha ⊢ <;> omega

theorem len_split {α : Type} (q r1 r2 : α → Bool) (h : ∀ k, q k = (r1 k || r2 k))
    (h' : ∀ k, ¬ (r1 k = true ∧ r2 k = true)) : ∀ l : List α,
    (l.filter q).length = (l.filter r1).length + (l.filter r2).length
  | [] => by simp
  | a :: l => by
    have ih := len_split q r1 r2 h h' l
    have ha := h a
    have ha' := h' a
    cases h1 : r1 a <;> cases h2 : r2 a <;> simp [List.filter_cons, h1, h2, ha] at ha' ⊢ <;> omega

theorem G_split (inj : ℕ → ℤ → Bool) (f : ℤ) (first : ℕ → ℤ → Bool)
    (tests : List (ℕ × ℤ × Bool)) (seeds : List ℕ) (d p : ℕ) (hp : p < 2^d) :
    G inj f first tests seeds d p = G inj f first tests seeds (d+1) p
      + G inj f first tests seeds (d+1) (p+2^d) := by
  unfold G
  apply len_split
  · intro k
    have hadd := block_add (first k) f d
    have hlt := block_lt (first k) f d
    generalize block (d+1) (first k) f = B' at *
    generalize block d (first k) f = B at *
    have hb := Bool.toNat_le (first k (f+1+(d:ℤ)))
    generalize (first k (f+1+(d:ℤ))).toNat = c at *
    generalize 2^d = P at *
    obtain hc | hc : c = 0 ∨ c = 1 := by omega
    · subst hc
      simp only [zero_mul, add_zero] at hadd
      subst hadd
      cases T inj first tests k
      · simp
      · rw [Bool.eq_iff_iff]
        simp only [Bool.and_true, Bool.or_eq_true, beq_iff_eq]
        omega
    · subst hc
      simp only [one_mul] at hadd
      subst hadd
      cases T inj first tests k
      · simp
      · rw [Bool.eq_iff_iff]
        simp only [Bool.and_true, Bool.or_eq_true, beq_iff_eq]
        omega
  · intro k
    have hadd := block_add (first k) f d
    generalize block (d+1) (first k) f = B' at *
    simp
    intro h1 _ h2
    omega

theorem body_step (inj : ℕ → ℤ → Bool) (f : ℤ) (ref : ℤ → Bool) (first : ℕ → ℤ → Bool)
    (tests : List (ℕ × ℤ × Bool)) (seeds : List ℕ) (mass : ℕ → ℕ → ℕ) (D : ℕ)
    (h1 : ∀ raw ∈ seeds, ∀ z ≤ f, first raw z = ref z)
    (h2 : ∀ h ≤ D, ∀ p < 2^h, mass h p = (seeds.filter (fun k => block h (first k) f == p)).length)
    (d : ℕ) (hd : d ≤ D) (a : ℕ) (ha : a < 2^d) (acc : ℕ × List ℕ)
    (hacc : ∀ l ∈ acc.2, l < 2^(d+1)) :
    (body inj f ref tests mass d acc a).1 + S inj f first tests seeds (d+1) (body inj f ref tests mass d acc a).2
      = acc.1 + S inj f first tests seeds (d+1) acc.2 + G inj f first tests seeds d a ∧
    ∀ l ∈ (body inj f ref tests mass d acc a).2, l < 2^(d+1) := by
  have hm := h2 d hd a ha
  have hle : G inj f first tests seeds d a ≤ mass d a := by
    rw [hm]; unfold G
    apply len_mono
    intro k _ hk
    simp only [Bool.and_eq_true] at hk
    exact hk.1
  unfold body
  simp only
  split_ifs with h0 hf ht
  · refine ⟨?_, hacc⟩
    omega
  · refine ⟨?_, hacc⟩
    have hmem : some false ∈ tests.map (observe inj f ref d a) := by simpa using hf
    obtain ⟨q, hq, hobs⟩ := List.mem_map.1 hmem
    have : G inj f first tests seeds d a ≤ 0 := by
      unfold G
      have := len_mono (fun k => (block d (first k) f == a) && T inj first tests k)
        (fun _ => false) seeds (by
          intro k hk hk2
          simp only [Bool.and_eq_true, beq_iff_eq] at hk2
          have hc := observe_correct inj f ref first k d a (h1 k hk) hk2.1 q false hobs
          have hT := hk2.2
          unfold T at hT
          rw [List.all_eq_true] at hT
          have := hT q hq
          rw [hc] at this
          exact this)
      simpa using this
    omega
  · refine ⟨?_, hacc⟩
    have hall : ∀ q ∈ tests, observe inj f ref d a q = some true := by
      intro q hq
      rw [List.all_eq_true] at ht
      have := ht _ (List.mem_map.2 ⟨q, hq, rfl⟩)
      simpa using this
    have : mass d a ≤ G inj f first tests seeds d a := by
      rw [hm]; unfold G
      apply len_mono
      intro k hk hk2
      simp only [Bool.and_eq_true, beq_iff_eq] at hk2 ⊢
      refine ⟨hk2, ?_⟩
      unfold T
      rw [List.all_eq_true]
      intro q hq
      have hc := observe_correct inj f ref first k d a (h1 k hk) hk2 q true (hall q hq)
      exact hc
    simp only
    omega
  · have hs := G_split inj f first tests seeds d a ha
    refine ⟨?_, ?_⟩
    · simp only [S, List.map_cons, List.sum_cons]
      rw [hs]
      omega
    · intro l hl
      simp only [List.mem_cons] at hl
      rw [pow_succ]
      rcases hl with rfl | rfl | hl
      · omega
      · omega
      · have := hacc l hl
        rw [pow_succ] at this
        exact this

theorem inner (inj : ℕ → ℤ → Bool) (f : ℤ) (ref : ℤ → Bool) (first : ℕ → ℤ → Bool)
    (tests : List (ℕ × ℤ × Bool)) (seeds : List ℕ) (mass : ℕ → ℕ → ℕ) (D : ℕ)
    (h1 : ∀ raw ∈ seeds, ∀ z ≤ f, first raw z = ref z)
    (h2 : ∀ h ≤ D, ∀ p < 2^h, mass h p = (seeds.filter (fun k => block h (first k) f == p)).length)
    (d : ℕ) (hd : d ≤ D) : ∀ (L : List ℕ) (acc : ℕ × List ℕ), (∀ l ∈ L, l < 2^d) →
    (∀ l ∈ acc.2, l < 2^(d+1)) →
    (L.foldl (body inj f ref tests mass d) acc).1
      + S inj f first tests seeds (d+1) (L.foldl (body inj f ref tests mass d) acc).2
      = acc.1 + S inj f first tests seeds (d+1) acc.2 + S inj f first tests seeds d L ∧
    (∀ l ∈ (L.foldl (body inj f ref tests mass d) acc).2, l < 2^(d+1))
  | [], acc, _, hacc => ⟨by simp [S], hacc⟩
  | a :: L, acc, hL, hacc => by
    obtain ⟨b1, b2⟩ := body_step inj f ref first tests seeds mass D h1 h2 d hd a (hL a (by simp)) acc hacc
    obtain ⟨i1, i2⟩ := inner inj f ref first tests seeds mass D h1 h2 d hd L
      (body inj f ref tests mass d acc a) (fun l hl => hL l (by simp [hl])) b2
    rw [List.foldl_cons]
    refine ⟨?_, i2⟩
    rw [i1, b1]
    simp only [S, List.map_cons, List.sum_cons]
    omega

theorem inner_last (inj : ℕ → ℤ → Bool) (f : ℤ) (ref : ℤ → Bool)
    (tests : List (ℕ × ℤ × Bool)) (mass : ℕ → ℕ → ℕ) (D : ℕ)
    (h3 : ∀ test ∈ tests, test.2.1 + 3*(test.1 : ℤ) ≤ f+(D : ℤ)) :
    ∀ (L : List ℕ) (acc : ℕ × List ℕ), (L.foldl (body inj f ref tests mass D) acc).2 = acc.2
  | [], acc => rfl
  | a :: L, acc => by
    rw [List.foldl_cons, inner_last inj f ref tests mass D h3 L]
    unfold body
    simp only
    split_ifs with h0 hf ht
    · rfl
    · rfl
    · rfl
    · exfalso
      apply ht
      rw [List.all_eq_true]
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      have hne := observe_some inj f ref D a q (h3 q hq)
      cases hv : observe inj f ref D a q with
      | none => exact absurd hv hne
      | some v =>
        cases v
        · exfalso
          apply hf
          have : some false ∈ tests.map (observe inj f ref D a) :=
            List.mem_map.2 ⟨q, hq, hv⟩
          simpa using this
        · rfl

theorem outer_inv (inj : ℕ → ℤ → Bool) (f : ℤ) (ref : ℤ → Bool) (first : ℕ → ℤ → Bool)
    (tests : List (ℕ × ℤ × Bool)) (seeds : List ℕ) (mass : ℕ → ℕ → ℕ) (D : ℕ)
    (h1 : ∀ raw ∈ seeds, ∀ z ≤ f, first raw z = ref z)
    (h2 : ∀ h ≤ D, ∀ p < 2^h, mass h p = (seeds.filter (fun k => block h (first k) f == p)).length) :
    ∀ n, n ≤ D + 1 →
    ((List.range n).foldl (outer inj f ref tests mass) (0, [0])).1
      + S inj f first tests seeds n ((List.range n).foldl (outer inj f ref tests mass) (0, [0])).2
      = (seeds.filter (T inj first tests)).length ∧
    ∀ l ∈ ((List.range n).foldl (outer inj f ref tests mass) (0, [0])).2, l < 2^n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [S, G, block]
  | succ n ih =>
    intro hn
    obtain ⟨i1, i2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (outer inj f ref tests mass) (0, [0]) = r at *
    obtain ⟨j1, j2⟩ := inner inj f ref first tests seeds mass D h1 h2 n (by omega) r.2 (r.1, [])
      i2 (by simp)
    unfold outer
    refine ⟨?_, j2⟩
    rw [j1]
    simp only [S, List.map_nil, List.sum_nil] at i1 ⊢
    omega

theorem main (D : ℕ) (f : ℤ) (inj : ℕ → ℤ → Bool) (seeds : List ℕ) (first : ℕ → ℤ → Bool)
    (ref : ℤ → Bool) (tests : List (ℕ × ℤ × Bool)) (mass : ℕ → ℕ → ℕ)
    (h1 : ∀ raw ∈ seeds, ∀ z ≤ f, first raw z = ref z)
    (h2 : ∀ h ≤ D, ∀ p < 2^h, mass h p = (seeds.filter (fun k => block h (first k) f == p)).length)
    (h3 : ∀ test ∈ tests, test.2.1 + 3*(test.1 : ℤ) ≤ f+(D : ℤ)) :
    ((List.range (D+1)).foldl (outer inj f ref tests mass) (0, [0])).2 = [] ∧
    ((List.range (D+1)).foldl (outer inj f ref tests mass) (0, [0])).1 =
      (seeds.filter (T inj first tests)).length := by
  have hlast : ((List.range (D+1)).foldl (outer inj f ref tests mass) (0, [0])).2 = [] := by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    unfold outer
    exact inner_last inj f ref tests mass D h3 _ _
  refine ⟨hlast, ?_⟩
  have := (outer_inv inj f ref first tests seeds mass D h1 h2 (D+1) le_rfl).1
  rw [hlast] at this
  simpa [S] using this

end PEqualNP.Outside.L_meta_25624_aux

theorem PEqualNP.Outside.L_meta_25624 :
let mix := fun (x : ℤ → Bool) (z : ℤ) => xor (xor (x (z-1)) (x z)) (x (z+1))
let step := fun (x injection : ℤ → Bool) (z : ℤ) =>
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (injection z)
let block := fun (w : ℕ) (tape : ℤ → Bool) (edge : ℤ) =>
  (List.range w).foldl (fun (code j : ℕ) => code ||| ((tape (edge+1+(j : ℤ))).toNat <<< j)) 0
∀ (w m D : ℕ) (b f : ℤ) (base : ℤ → Bool) (inj : ℕ → ℤ → Bool) (mask : ℕ)
    (tests : List (ℕ × ℤ × Bool)) (mass : ℕ → ℕ → ℕ),
  let seeds := (List.range (2^m)).filter (fun raw => mask.testBit (raw % 2^w))
  let first := fun (raw : ℕ) => step (fun inputSite => if inputSite ≤ b then base inputSite else raw.testBit (inputSite-b-1).toNat) (inj 0)
  let ref := step base (inj 0)
  (∀ raw ∈ seeds, ∀ z ≤ f, first raw z = ref z) →
  (∀ h ≤ D, ∀ p < 2^h, mass h p = (seeds.filter (fun k => block h (first k) f == p)).length) →
  (∀ test ∈ tests, test.2.1 + 3*(test.1 : ℤ) ≤ f+(D : ℤ)) →
  let actual := fun (seed time : ℕ) =>
    (List.range time).foldl (fun state tick => step state (inj (tick+1))) (first seed)
  let observe := fun (width pattern : ℕ) (query : ℕ × ℤ × Bool) =>
    let sample := fun (site : ℤ) => if site ≤ f then ref site else pattern.testBit (site-f-1).toNat
    let pair := (List.range query.1).foldl (fun (prev : (ℤ → Bool) × ℤ) j =>
      (step prev.1 (inj (j+1)), prev.2-3+((mix prev.1 (prev.2-1)).toNat : ℤ)))
      (sample, f+(width : ℤ))
    if query.2.1 ≤ pair.2 then some (pair.1 query.2.1 == query.2.2) else none
  let tally := (List.range (D+1)).foldl (fun (layer : ℕ × List ℕ) depth =>
    layer.2.foldl (fun (acc : ℕ × List ℕ) label =>
      let weight := mass depth label
      if weight = 0 then acc else
        let answers := tests.map (observe depth label)
        if answers.contains (some false) then acc
        else if answers.all (fun answer => answer == some true) then (acc.1+weight, acc.2)
        else (acc.1, label :: (label + 2^depth) :: acc.2))
      (layer.1, [])) (0, [0])
  tally.2 = [] ∧ tally.1 =
    (seeds.filter (fun key => tests.all (fun wanted => actual key wanted.1 wanted.2.1 == wanted.2.2))).length := by
  intro mix step block w m D b f base inj mask tests mass seeds first ref h1 h2 h3 actual observe tally
  exact PEqualNP.Outside.L_meta_25624_aux.main D f inj seeds first ref tests mass h1 h2 h3
