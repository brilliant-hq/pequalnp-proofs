import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta507

open Turing

abbrev KK (s D : ℕ) : Type := Bool ⊕ Option (Fin s ⊕ Fin (D + 1))

abbrev St (s D : ℕ) (Λ : Type) : Type := TM2.Stmt (fun _ : KK s D => Bool) Λ (Option Bool)

abbrev Cf (s D : ℕ) (Λ : Type) : Type := TM2.Cfg (fun _ : KK s D => Bool) Λ (Option Bool)

def kI {s D : ℕ} : KK s D := Sum.inl false
def kO {s D : ℕ} : KK s D := Sum.inl true
def kT {s D : ℕ} : KK s D := Sum.inr none
def kX {s D : ℕ} (i : Fin s) : KK s D := Sum.inr (some (Sum.inl i))
def kC {s D : ℕ} (l : ℕ) : KK s D := Sum.inr (some (Sum.inr ⟨min l D, by omega⟩))

def stk {s D : ℕ} (a o t : List Bool) (x : Fin s → List Bool) (c : ℕ → List Bool) :
    KK s D → List Bool
  | Sum.inl false => a
  | Sum.inl true => o
  | Sum.inr none => t
  | Sum.inr (some (Sum.inl i)) => x i
  | Sum.inr (some (Sum.inr j)) => c j.val

section
variable {s D : ℕ} (a o t : List Bool) (x : Fin s → List Bool) (c : ℕ → List Bool)

@[simp] theorem stk_I : stk (D := D) a o t x c kI = a := rfl
@[simp] theorem stk_O : stk (D := D) a o t x c kO = o := rfl
@[simp] theorem stk_T : stk (D := D) a o t x c kT = t := rfl
@[simp] theorem stk_X (i : Fin s) : stk (D := D) a o t x c (kX i) = x i := rfl
theorem stk_C (l : ℕ) (h : l ≤ D) : stk (D := D) a o t x c (kC l) = c l := by
  simp [stk, kC, Nat.min_eq_left h]

@[simp] theorem upd_I (a' : List Bool) :
    Function.update (stk (D := D) a o t x c) kI a' = stk a' o t x c := by
  funext k
  rcases k with (_ | _) | (_ | (_ | _)) <;> simp [stk, kI, Function.update_apply]

@[simp] theorem upd_O (o' : List Bool) :
    Function.update (stk (D := D) a o t x c) kO o' = stk a o' t x c := by
  funext k
  rcases k with (_ | _) | (_ | (_ | _)) <;> simp [stk, kO, Function.update_apply]

@[simp] theorem upd_T (t' : List Bool) :
    Function.update (stk (D := D) a o t x c) kT t' = stk a o t' x c := by
  funext k
  rcases k with (_ | _) | (_ | (_ | _)) <;> simp [stk, kT, Function.update_apply]

@[simp] theorem upd_X (i : Fin s) (v : List Bool) :
    Function.update (stk (D := D) a o t x c) (kX i) v = stk a o t (Function.update x i v) c := by
  funext k
  rcases k with (_ | _) | (_ | (_ | _)) <;> simp [stk, kX, Function.update_apply]

theorem upd_C (l : ℕ) (h : l ≤ D) (v : List Bool) :
    Function.update (stk (D := D) a o t x c) (kC l) v = stk a o t x (Function.update c l v) := by
  funext k
  rcases k with (_ | _) | (_ | (_ | j))
  · simp [stk, kC, Function.update_apply]
  · simp [stk, kC, Function.update_apply]
  · simp [stk, kC, Function.update_apply]
  · simp [stk, kC, Function.update_apply]
  · simp only [stk, kC, Function.update_apply]
    have : (Sum.inr (some (Sum.inr j)) : KK s D) = Sum.inr (some (Sum.inr ⟨min l D, by omega⟩))
        ↔ j.val = l := by
      simp [Fin.ext_iff, Nat.min_eq_left h]
    by_cases hj : j.val = l
    · rw [if_pos (this.mpr hj), if_pos hj]
    · rw [if_neg (fun e => hj (this.mp e)), if_neg hj]

end


section
variable {s D : ℕ} {Λ : Type}

def go (lab : ℕ → Λ) (l : ℕ) : St s D Λ :=
  TM2.Stmt.load (fun _ => none) (TM2.Stmt.goto (fun _ => lab l))

def pu (k : KK s D) (q : St s D Λ) : St s D Λ := TM2.Stmt.push k (fun _ => true) q

def puF (k : KK s D) (q : St s D Λ) : St s D Λ := TM2.Stmt.push k (fun _ => false) q

def po (k : KK s D) (qn qf qt : St s D Λ) : St s D Λ :=
  TM2.Stmt.pop k (fun _ o => o)
    (TM2.Stmt.branch (fun v => v.isSome) (TM2.Stmt.branch (fun v => v.getD false) qt qf) qn)

def adv (M : Λ → St s D Λ) : Option (Cf s D Λ) → Option (Cf s D Λ) := flip bind (TM2.step M)

theorem adv_s (M : Λ → St s D Λ) (l : Λ) (v : Option Bool) (S : KK s D → List Bool) :
    adv M (some ⟨some l, v, S⟩) = some (TM2.stepAux (M l) v S) := rfl

theorem sa_go (lab : ℕ → Λ) (l : ℕ) (v : Option Bool) (S : KK s D → List Bool) :
    TM2.stepAux (go lab l : St s D Λ) v S = ⟨some (lab l), none, S⟩ := rfl

theorem sa_pu (k : KK s D) (q : St s D Λ) (v : Option Bool) (S : KK s D → List Bool) :
    TM2.stepAux (pu k q) v S = TM2.stepAux q v (Function.update S k (true :: S k)) := rfl

theorem sa_puF (k : KK s D) (q : St s D Λ) (v : Option Bool) (S : KK s D → List Bool) :
    TM2.stepAux (puF k q) v S = TM2.stepAux q v (Function.update S k (false :: S k)) := rfl

theorem sa_po_n {k : KK s D} {qn qf qt : St s D Λ} {v : Option Bool} {S : KK s D → List Bool}
    (h : S k = []) : TM2.stepAux (po k qn qf qt) v S = TM2.stepAux qn none S := by
  unfold po
  simp only [TM2.stepAux, h, List.head?_nil, List.tail_nil, Option.isSome_none, cond_false]
  rw [← h, Function.update_eq_self]

theorem sa_po_t {k : KK s D} {qn qf qt : St s D Λ} {v : Option Bool} {S : KK s D → List Bool}
    {r : List Bool} (h : S k = true :: r) :
    TM2.stepAux (po k qn qf qt) v S = TM2.stepAux qt (some true) (Function.update S k r) := by
  simp only [po, TM2.stepAux, h]
  rfl

theorem sa_po_f {k : KK s D} {qn qf qt : St s D Λ} {v : Option Bool} {S : KK s D → List Bool}
    {r : List Bool} (h : S k = false :: r) :
    TM2.stepAux (po k qn qf qt) v S = TM2.stepAux qf (some false) (Function.update S k r) := by
  simp only [po, TM2.stepAux, h]
  rfl

theorem itc {α : Type} {f : α → α} {a b : ℕ} {x y z : α} (h1 : f^[a] x = y) (h2 : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

theorem it1 {α : Type} {f : α → α} {x y : α} (h : f x = y) : f^[1] x = y := h

abbrev rep (n : ℕ) : List Bool := List.replicate n true

def copyS (lab : ℕ → Λ) (i : Fin s) (ℓ l : ℕ) : St s D Λ :=
  po (kX i) (go lab (l + 1)) (pu kT (pu (kC ℓ) (go lab l))) (pu kT (pu (kC ℓ) (go lab l)))

def restS (lab : ℕ → Λ) (i : Fin s) (l : ℕ) : St s D Λ :=
  po kT (go lab (l + 1)) (pu (kX i) (go lab l)) (pu (kX i) (go lab l))

def mainS (lab : ℕ → Λ) (ℓ l e : ℕ) : St s D Λ :=
  po (kC ℓ) (go lab e) (go lab (l + 1)) (go lab (l + 1))

variable (lab : ℕ → Λ) (M : Λ → St s D Λ)

theorem copyLoop (i : Fin s) (ℓ l : ℕ) (hℓ : ℓ ≤ D) (hM : M (lab l) = copyS lab i ℓ l) (o : List Bool) :
    ∀ (m tt cc : ℕ) (x : Fin s → List Bool) (c : ℕ → List Bool) (v : Option Bool),
      x i = rep m → c ℓ = rep cc →
      (adv M)^[m + 1] (some ⟨some (lab l), v, stk [] o (rep tt) x c⟩) =
        some ⟨some (lab (l + 1)), none,
          stk [] o (rep (m + tt)) (Function.update x i []) (Function.update c ℓ (rep (m + cc)))⟩ := by
  intro m
  induction m with
  | zero =>
    intro tt cc x c v hx hc
    rw [it1 (by rw [adv_s, hM, copyS, sa_po_n (by rw [stk_X, hx]; rfl), sa_go])]
    have e1 : Function.update x i [] = x := Function.update_eq_self_iff.mpr (by rw [hx]; rfl)
    have e2 : Function.update c ℓ (rep (0 + cc)) = c :=
      Function.update_eq_self_iff.mpr (by rw [hc, Nat.zero_add])
    rw [e1, e2, Nat.zero_add]
  | succ m ih =>
    intro tt cc x c v hx hc
    rw [Function.iterate_succ_apply]
    rw [adv_s, hM, copyS, sa_po_t (by rw [stk_X, hx]; rfl), sa_pu, sa_pu, sa_go]
    simp only [upd_X, upd_T, stk_T, upd_C _ _ _ _ _ _ hℓ, stk_C _ _ _ _ _ _ hℓ]
    rw [hc]
    have := ih (tt + 1) (cc + 1) (Function.update x i (rep m)) (Function.update c ℓ (rep (cc + 1))) none
      (by simp) (by simp)
    rw [show true :: rep tt = rep (tt + 1) from rfl, show true :: rep cc = rep (cc + 1) from rfl,
      this]
    simp only [Function.update_idem]
    rw [show m + (tt + 1) = m + 1 + tt by omega, show m + (cc + 1) = m + 1 + cc by omega]


theorem restLoop (i : Fin s) (l : ℕ) (hM : M (lab l) = restS lab i l) (o : List Bool)
    (c : ℕ → List Bool) :
    ∀ (m xx : ℕ) (x : Fin s → List Bool) (v : Option Bool), x i = rep xx →
      (adv M)^[m + 1] (some ⟨some (lab l), v, stk [] o (rep m) x c⟩) =
        some ⟨some (lab (l + 1)), none, stk [] o [] (Function.update x i (rep (m + xx))) c⟩ := by
  intro m
  induction m with
  | zero =>
    intro xx x v hx
    rw [it1 (by rw [adv_s, hM, restS, sa_po_n (by rw [stk_T]; rfl), sa_go])]
    have e1 : Function.update x i (rep (0 + xx)) = x :=
      Function.update_eq_self_iff.mpr (by rw [hx, Nat.zero_add])
    rw [e1]
    rfl
  | succ m ih =>
    intro xx x v hx
    rw [Function.iterate_succ_apply]
    rw [adv_s, hM, restS, sa_po_t (by rw [stk_T]; rfl), sa_pu, sa_go]
    simp only [upd_X, upd_T, stk_X]
    rw [hx]
    have := ih (xx + 1) (Function.update x i (rep (xx + 1))) none (by simp)
    rw [show true :: rep xx = rep (xx + 1) from rfl, this]
    simp only [Function.update_idem]
    rw [show m + (xx + 1) = m + 1 + xx by omega]

theorem mainLoop (ℓ l e : ℕ) (hℓ : ℓ ≤ D) (hM : M (lab l) = mainS lab ℓ l e)
    (x : Fin s → List Bool) (Ti p : ℕ)
    (hin : ∀ (o : List Bool) (c : ℕ → List Bool), (∀ j, ℓ < j → c j = []) →
      (adv M)^[Ti] (some ⟨some (lab (l + 1)), none, stk [] o [] x c⟩) =
        some ⟨some (lab l), none, stk [] (rep p ++ o) [] x c⟩) :
    ∀ (m : ℕ) (o : List Bool) (c : ℕ → List Bool) (v : Option Bool), c ℓ = rep m →
      (∀ j, ℓ < j → c j = []) →
      (adv M)^[m * (Ti + 1) + 1] (some ⟨some (lab l), v, stk [] o [] x c⟩) =
        some ⟨some (lab e), none, stk [] (rep (m * p) ++ o) [] x (Function.update c ℓ [])⟩ := by
  intro m
  induction m with
  | zero =>
    intro o c v hc _
    rw [Nat.zero_mul, Nat.zero_add]
    rw [it1 (by rw [adv_s, hM, mainS, sa_po_n (by rw [stk_C _ _ _ _ _ _ hℓ, hc]; rfl), sa_go])]
    have e1 : Function.update c ℓ [] = c := Function.update_eq_self_iff.mpr (by rw [hc]; rfl)
    rw [e1, Nat.zero_mul]
    rfl
  | succ m ih =>
    intro o c v hc hj
    rw [show (m + 1) * (Ti + 1) + 1 = 1 + (Ti + (m * (Ti + 1) + 1)) by ring]
    have hs : adv M (some ⟨some (lab l), v, stk [] o [] x c⟩) =
        some (⟨some (lab (l + 1)), none, stk [] o [] x (Function.update c ℓ (rep m))⟩ :
          Cf s D Λ) := by
      rw [adv_s, hM, mainS, sa_po_t (by rw [stk_C _ _ _ _ _ _ hℓ, hc]; rfl), sa_go,
        upd_C _ _ _ _ _ _ hℓ]
    refine itc (it1 hs) (itc (hin o (Function.update c ℓ (rep m)) ?_) ?_)
    · intro j hlj
      rw [Function.update_of_ne (by omega)]
      exact hj j hlj
    · rw [ih (rep p ++ o) (Function.update c ℓ (rep m)) none (by simp) (by
        intro j hlj
        rw [Function.update_of_ne (by omega)]
        exact hj j hlj)]
      simp only [Function.update_idem, ← List.append_assoc, ← List.replicate_add]
      rw [show m * p + p = (m + 1) * p by ring]

def monoF (lab : ℕ → Λ) : List (Fin s) → ℕ → ℕ → ℕ → ℕ → St s D Λ
  | [], _, _, e, _ => pu kO (go lab e)
  | i :: L, ℓ, b, e, r =>
    if r = 0 then copyS lab i ℓ b
    else if r = 1 then restS lab i (b + 1)
    else if r = 2 then mainS lab ℓ (b + 2) e
    else monoF lab L (ℓ + 1) (b + 3) (b + 2) (r - 3)

def Loc (b n : ℕ) (f : ℕ → St s D Λ) : Prop := ∀ r, r < n → M (lab (b + r)) = f r

def monoTime (v : Fin s → ℕ) : List (Fin s) → ℕ
  | [] => 1
  | i :: L => (v i + 1) + ((v i + 1) + (v i * (monoTime v L + 1) + 1))

theorem monoSpec (v : Fin s → ℕ) (x : Fin s → List Bool) (hx : ∀ i, x i = rep (v i)) :
    ∀ (L : List (Fin s)) (ℓ b e : ℕ) (c : ℕ → List Bool) (o : List Bool),
      Loc lab M b (3 * L.length + 1) (monoF lab L ℓ b e) → ℓ + L.length ≤ D + 1 →
      (∀ j, ℓ ≤ j → c j = []) →
      (adv M)^[monoTime v L] (some ⟨some (lab b), none, stk [] o [] x c⟩) =
        some ⟨some (lab e), none, stk [] (rep ((L.map v).prod) ++ o) [] x c⟩ := by
  intro L
  induction L with
  | nil =>
    intro ℓ b e c o hL _ _
    have h0 := hL 0 (by simp)
    rw [Nat.add_zero] at h0
    rw [monoTime, it1 (by rw [adv_s, h0, monoF, sa_pu, sa_go, upd_O, stk_O])]
    rfl
  | cons i L ih =>
    intro ℓ b e c o hL hD hc
    have hℓ : ℓ ≤ D := by simp at hD; omega
    have h0 : M (lab b) = copyS lab i ℓ b := by
      have := hL 0 (by simp); rw [Nat.add_zero] at this; rw [this]; simp [monoF]
    have h1 : M (lab (b + 1)) = restS lab i (b + 1) := by
      have := hL 1 (by simp); rw [this]; simp [monoF]
    have h2 : M (lab (b + 2)) = mainS lab ℓ (b + 2) e := by
      have := hL 2 (by simp; omega); rw [this]; simp [monoF]
    have h3 : Loc lab M (b + 3) (3 * L.length + 1) (monoF lab L (ℓ + 1) (b + 3) (b + 2)) := by
      intro r hr
      have := hL (r + 3) (by simp; omega)
      rw [show b + 3 + r = b + (r + 3) by omega, this]
      simp [monoF]
    have hc0 : c ℓ = rep 0 := hc ℓ le_rfl
    have hA := copyLoop lab M i ℓ b hℓ h0 o (v i) 0 0 x c none (hx i) hc0
    have hB := restLoop lab M i (b + 1) h1 o (Function.update c ℓ (rep (v i + 0))) (v i + 0) 0
      (Function.update x i []) none (by simp)
    have ex : Function.update (Function.update x i []) i (rep (v i + 0 + 0)) = x := by
      rw [Function.update_idem]; exact Function.update_eq_self_iff.mpr (by rw [hx i]; simp)
    simp only [Nat.add_zero] at hA hB ex
    rw [ex, show b + 1 + 1 = b + 2 by omega] at hB
    have hC := mainLoop lab M ℓ (b + 2) e hℓ h2 x (monoTime v L) ((L.map v).prod)
      (fun o' c' hc' => ih (ℓ + 1) (b + 3) (b + 2) c' o' h3 (by simp at hD; omega)
        (fun j hj => hc' j (by omega)))
      (v i + 0) o (Function.update c ℓ (rep (v i + 0))) none (by simp) (by
        intro j hj; rw [Function.update_of_ne (by omega)]; exact hc j (by omega))
    have ec : Function.update (Function.update c ℓ (rep (v i + 0))) ℓ [] = c := by
      rw [Function.update_idem]; exact Function.update_eq_self_iff.mpr (hc ℓ le_rfl).symm
    simp only [Nat.add_zero] at hC ec
    rw [ec] at hC
    rw [monoTime]
    refine itc hA (itc hB ?_)
    rw [hC, List.map_cons, List.prod_cons]


def jobSize : Option (List (Fin s)) → ℕ
  | none => 1
  | some L => 3 * L.length + 1

def jobF (lab : ℕ → Λ) : Option (List (Fin s)) → ℕ → ℕ → St s D Λ
  | none, b, _ => puF kO (go lab (b + 1))
  | some L, b, r => monoF lab L 0 b (b + (3 * L.length + 1)) r

def seqSize : List (Option (List (Fin s))) → ℕ
  | [] => 0
  | j :: J => jobSize j + seqSize J

def seqF (lab : ℕ → Λ) : List (Option (List (Fin s))) → ℕ → ℕ → St s D Λ
  | [], _, _ => TM2.Stmt.halt
  | j :: J, b, r =>
    if r < jobSize j then jobF lab j b r else seqF lab J (b + jobSize j) (r - jobSize j)

def jobOut (v : Fin s → ℕ) : Option (List (Fin s)) → List Bool
  | none => [false]
  | some L => rep ((L.map v).prod)

def seqOut (v : Fin s → ℕ) : List (Option (List (Fin s))) → List Bool → List Bool
  | [], o => o
  | j :: J, o => seqOut v J (jobOut v j ++ o)

def jobTime (v : Fin s → ℕ) : Option (List (Fin s)) → ℕ
  | none => 1
  | some L => monoTime v L

def seqTime (v : Fin s → ℕ) : List (Option (List (Fin s))) → ℕ
  | [] => 0
  | j :: J => jobTime v j + seqTime v J

def jobOk (D : ℕ) : Option (List (Fin s)) → Prop
  | none => True
  | some L => L.length ≤ D + 1

theorem jobSpec (v : Fin s → ℕ) (x : Fin s → List Bool) (hx : ∀ i, x i = rep (v i))
    (j : Option (List (Fin s))) (b : ℕ) (o : List Bool)
    (hL : Loc lab M b (jobSize j) (jobF lab j b)) (hj : jobOk D j) :
    (adv M)^[jobTime v j] (some ⟨some (lab b), none, stk [] o [] x (fun _ => [])⟩) =
      some ⟨some (lab (b + jobSize j)), none, stk [] (jobOut v j ++ o) [] x (fun _ => [])⟩ := by
  cases j with
  | none =>
    have h0 := hL 0 (by simp [jobSize])
    rw [Nat.add_zero] at h0
    rw [jobTime, it1 (by rw [adv_s, h0, jobF, sa_puF, sa_go, upd_O, stk_O])]
    rfl
  | some L =>
    exact monoSpec lab M v x hx L 0 b _ _ o hL (by simp [jobOk] at hj; omega) (fun _ _ => rfl)

theorem seqSpec (v : Fin s → ℕ) (x : Fin s → List Bool) (hx : ∀ i, x i = rep (v i)) :
    ∀ (J : List (Option (List (Fin s)))) (b : ℕ) (o : List Bool),
      Loc lab M b (seqSize J) (seqF lab J b) → (∀ j ∈ J, jobOk D j) →
      (adv M)^[seqTime v J] (some ⟨some (lab b), none, stk [] o [] x (fun _ => [])⟩) =
        some ⟨some (lab (b + seqSize J)), none, stk [] (seqOut v J o) [] x (fun _ => [])⟩ := by
  intro J
  induction J with
  | nil => intro b o _ _; rfl
  | cons j J ih =>
    intro b o hL hJ
    have h1 : Loc lab M b (jobSize j) (jobF lab j b) := by
      intro r hr
      rw [hL r (by simp [seqSize]; omega)]
      simp [seqF, hr]
    have h2 : Loc lab M (b + jobSize j) (seqSize J) (seqF lab J (b + jobSize j)) := by
      intro r hr
      rw [show b + jobSize j + r = b + (jobSize j + r) by omega, hL _ (by simp [seqSize]; omega)]
      simp [seqF]
    rw [seqTime]
    refine itc (jobSpec lab M v x hx j b o h1 (hJ j (by simp))) ?_
    rw [ih (b + jobSize j) _ h2 (fun j' hj' => hJ j' (by simp [hj'])), seqSize, seqOut,
      Nat.add_assoc]

def parseF (lab : ℕ → Λ) (e : ℕ) (r : ℕ) : St s D Λ :=
  if r % 2 = 0 then po kI (go lab e) (go lab e) (go lab (r + 1))
  else if h : r / 2 < s then
    po kI (go lab e) (go lab (2 * min (r / 2 + 1) s)) (pu (kX ⟨r / 2, h⟩) (go lab r))
  else po kI (go lab e) (go lab (2 * min (r / 2 + 1) s)) (go lab r)

def regAdd (x : Fin s → List Bool) (i a : ℕ) : Fin s → List Bool :=
  fun j => if j.val = i then rep a ++ x j else x j

theorem regAdd_regAdd (x : Fin s → List Bool) (i a b : ℕ) :
    regAdd (regAdd x i a) i b = regAdd x i (b + a) := by
  funext j
  unfold regAdd
  by_cases h : j.val = i
  · simp only [h, if_true]
    rw [← List.append_assoc, ← List.replicate_add]
  · simp only [h, if_false]

theorem regAdd_zero (x : Fin s → List Bool) (i : ℕ) : regAdd x i 0 = x := by
  funext j; unfold regAdd; split_ifs <;> rfl

theorem parseQ_t (e i : ℕ) (hP : ∀ r, r < 2 * s + 2 → M (lab r) = parseF lab e r)
    (rest : List Bool) (x : Fin s → List Bool) (c : ℕ → List Bool) (v : Option Bool) :
    adv M (some ⟨some (lab (2 * min i s + 1)), v, stk (true :: rest) [] [] x c⟩) =
      some ⟨some (lab (2 * min i s + 1)), none, stk rest [] [] (regAdd x i 1) c⟩ := by
  rw [adv_s, hP _ (by omega), parseF]
  have e1 : (2 * min i s + 1) % 2 = 1 := by omega
  have e2 : (2 * min i s + 1) / 2 = min i s := by omega
  rw [if_neg (by omega)]
  by_cases hi : i < s
  · have e3 : (2 * min i s + 1) / 2 < s := by omega
    rw [dif_pos e3, sa_po_t (by rfl), sa_pu, sa_go]
    simp only [upd_I, upd_X, stk_X]
    have key : (⟨(2 * min i s + 1) / 2, e3⟩ : Fin s) = ⟨i, hi⟩ := Fin.ext (by simp only; omega)
    rw [key]
    congr 3
    funext j
    unfold regAdd
    by_cases h : j.val = i
    · have : j = ⟨i, hi⟩ := Fin.ext h
      subst this
      simp
    · rw [Function.update_of_ne (fun e => h (by rw [e])), if_neg h]
  · have e3 : ¬ (2 * min i s + 1) / 2 < s := by omega
    rw [dif_neg e3, sa_po_t (by rfl), sa_go]
    simp only [upd_I]
    congr 3
    funext j
    unfold regAdd
    rw [if_neg (by omega)]

theorem parseQ_f (e i : ℕ) (hP : ∀ r, r < 2 * s + 2 → M (lab r) = parseF lab e r)
    (rest : List Bool) (x : Fin s → List Bool) (c : ℕ → List Bool) (v : Option Bool) :
    adv M (some ⟨some (lab (2 * min i s + 1)), v, stk (false :: rest) [] [] x c⟩) =
      some ⟨some (lab (2 * min (i + 1) s)), none, stk rest [] [] x c⟩ := by
  rw [adv_s, hP _ (by omega), parseF]
  have e2 : (2 * min i s + 1) / 2 = min i s := by omega
  have e4 : min (min i s + 1) s = min (i + 1) s := by omega
  rw [if_neg (by omega)]
  split_ifs
  · rw [sa_po_f (by rfl), sa_go, upd_I, e2, e4]
  · rw [sa_po_f (by rfl), sa_go, upd_I, e2, e4]

theorem parseP_t (e i : ℕ) (hP : ∀ r, r < 2 * s + 2 → M (lab r) = parseF lab e r)
    (rest : List Bool) (x : Fin s → List Bool) (c : ℕ → List Bool) (v : Option Bool) :
    adv M (some ⟨some (lab (2 * min i s)), v, stk (true :: rest) [] [] x c⟩) =
      some ⟨some (lab (2 * min i s + 1)), none, stk rest [] [] x c⟩ := by
  rw [adv_s, hP _ (by omega), parseF, if_pos (by omega), sa_po_t (by rfl), sa_go, upd_I]

theorem parseP_f (e i : ℕ) (hP : ∀ r, r < 2 * s + 2 → M (lab r) = parseF lab e r)
    (rest : List Bool) (x : Fin s → List Bool) (c : ℕ → List Bool) (v : Option Bool) :
    adv M (some ⟨some (lab (2 * min i s)), v, stk (false :: rest) [] [] x c⟩) =
      some ⟨some (lab e), none, stk rest [] [] x c⟩ := by
  rw [adv_s, hP _ (by omega), parseF, if_pos (by omega), sa_po_f (by rfl), sa_go, upd_I]

theorem digitLoop (e i : ℕ) (hP : ∀ r, r < 2 * s + 2 → M (lab r) = parseF lab e r)
    (rest : List Bool) (c : ℕ → List Bool) :
    ∀ (a : ℕ) (x : Fin s → List Bool) (v : Option Bool),
      (adv M)^[a + 1] (some ⟨some (lab (2 * min i s + 1)), v, stk (rep a ++ false :: rest) [] [] x c⟩) =
        some ⟨some (lab (2 * min (i + 1) s)), none, stk rest [] [] (regAdd x i a) c⟩ := by
  intro a
  induction a with
  | zero =>
    intro x v
    rw [regAdd_zero]
    exact it1 (parseQ_f lab M e i hP rest x c v)
  | succ a ih =>
    intro x v
    rw [Function.iterate_succ_apply]
    rw [show rep (a + 1) ++ false :: rest = true :: (rep a ++ false :: rest) from rfl,
      parseQ_t lab M e i hP, ih, regAdd_regAdd]


abbrev encN (t : List ℕ) : List Bool :=
  PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]) t

theorem encN_nil : encN [] = [false] := by
  simp [encN, PEqualNP.CircuitLowerBounds.encodeList]

theorem encN_cons (a : ℕ) (t : List ℕ) : encN (a :: t) = true :: (rep a ++ false :: encN t) := by
  simp [encN, PEqualNP.CircuitLowerBounds.encodeList]

theorem parseSpec (e : ℕ) (hP : ∀ r, r < 2 * s + 2 → M (lab r) = parseF lab e r)
    (c : ℕ → List Bool) :
    ∀ (t : List ℕ) (i : ℕ) (x : Fin s → List Bool), (∀ j : Fin s, i ≤ j.val → x j = []) →
      (adv M)^[(encN t).length] (some ⟨some (lab (2 * min i s)), none, stk (encN t) [] [] x c⟩) =
        some ⟨some (lab e), none,
          stk [] [] [] (fun j => if j.val < i then x j else rep (t.getD (j.val - i) 0)) c⟩ := by
  intro t
  induction t with
  | nil =>
    intro i x hx
    rw [encN_nil, show [false].length = 1 from rfl, it1 (parseP_f lab M e i hP [] x c none)]
    congr 4
    funext j
    split_ifs with h
    · rfl
    · rw [hx j (by omega)]; simp
  | cons a t ih =>
    intro i x hx
    have hl : (encN (a :: t)).length = 1 + ((a + 1) + (encN t).length) := by
      rw [encN_cons]; simp; omega
    have hreg : ∀ j : Fin s, i + 1 ≤ j.val → regAdd x i a j = [] := by
      intro j hj
      unfold regAdd
      rw [if_neg (by omega)]
      exact hx j (by omega)
    have h3 := ih (i + 1) (regAdd x i a) hreg
    have hfun : (fun j : Fin s => if j.val < i + 1 then regAdd x i a j
        else rep (t.getD (j.val - (i + 1)) 0)) =
        (fun j : Fin s => if j.val < i then x j else rep ((a :: t).getD (j.val - i) 0)) := by
      funext j
      unfold regAdd
      by_cases h1 : j.val < i
      · rw [if_pos (by omega), if_neg (by omega), if_pos h1]
      · by_cases h2 : j.val = i
        · rw [if_pos (by omega), if_pos h2, if_neg h1, hx j (by omega), h2, Nat.sub_self]
          simp
        · rw [if_neg (by omega), if_neg h1, show j.val - i = (j.val - (i + 1)) + 1 by omega]
          simp
    rw [hfun] at h3
    rw [hl, encN_cons]
    refine itc (it1 (parseP_t lab M e i hP _ x c none)) (itc (digitLoop lab M e i hP _ c a x none) ?_)
    exact h3

def cleanF (lab : ℕ → Λ) (b : ℕ) (r : ℕ) : St s D Λ :=
  if h : r < s then po (kX ⟨r, h⟩) (go lab (b + r + 1)) (go lab (b + r)) (go lab (b + r))
  else TM2.Stmt.halt

theorem clearLoop (b r : ℕ) (hr : r < s) (hM : M (lab (b + r)) = cleanF lab b r) (o : List Bool)
    (c : ℕ → List Bool) :
    ∀ (m : ℕ) (x : Fin s → List Bool) (v : Option Bool), x ⟨r, hr⟩ = rep m →
      (adv M)^[m + 1] (some ⟨some (lab (b + r)), v, stk [] o [] x c⟩) =
        some ⟨some (lab (b + r + 1)), none, stk [] o [] (Function.update x ⟨r, hr⟩ []) c⟩ := by
  intro m
  induction m with
  | zero =>
    intro x v hx
    rw [it1 (by rw [adv_s, hM, cleanF, dif_pos hr, sa_po_n (by rw [stk_X, hx]; rfl), sa_go])]
    rw [Function.update_eq_self_iff.mpr (by rw [hx]; rfl)]
  | succ m ih =>
    intro x v hx
    rw [Function.iterate_succ_apply]
    rw [adv_s, hM, cleanF, dif_pos hr, sa_po_t (by rw [stk_X, hx]; rfl), sa_go, upd_X,
      ih _ none (by simp), Function.update_idem]

def vN (val : Fin s → ℕ) (j : ℕ) : ℕ := if h : j < s then val ⟨j, h⟩ else 0

theorem cleanAll (b : ℕ) (hC : ∀ r, r < s + 1 → M (lab (b + r)) = cleanF lab b r) (o : List Bool)
    (c : ℕ → List Bool) (val : Fin s → ℕ) (x : Fin s → List Bool) (hx : ∀ j, x j = rep (val j)) :
    ∀ r, r ≤ s →
      (adv M)^[∑ j ∈ Finset.range r, (vN val j + 1)] (some ⟨some (lab b), none, stk [] o [] x c⟩) =
        some ⟨some (lab (b + r)), none, stk [] o [] (fun j => if j.val < r then [] else x j) c⟩ := by
  intro r
  induction r with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.sum_empty, Function.iterate_zero, id, Nat.add_zero]
    congr 4
  | succ r ih =>
    intro hr
    rw [Finset.sum_range_succ]
    have hr' : r < s := by omega
    refine itc (ih (by omega)) ?_
    have := clearLoop lab M b r hr' (hC r (by omega)) o c (val ⟨r, hr'⟩)
      (fun j => if j.val < r then [] else x j) none (by simp [hx])
    rw [show vN val r = val ⟨r, hr'⟩ by simp [vN, hr'], this, Nat.add_assoc]
    congr 4
    funext j
    by_cases h : j.val = r
    · have : j = ⟨r, hr'⟩ := Fin.ext h
      subst this
      simp
    · rw [Function.update_of_ne (fun e => h (by rw [e]))]
      by_cases h2 : j.val < r
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

end

def progF {s D : ℕ} {Λ : Type} (lab : ℕ → Λ) (J : List (Option (List (Fin s)))) (r : ℕ) :
    St s D Λ :=
  if r < 2 * s + 2 then parseF lab (2 * s + 2) r
  else if r < 2 * s + 2 + seqSize J then seqF lab J (2 * s + 2) (r - (2 * s + 2))
  else cleanF lab (2 * s + 2 + seqSize J) (r - (2 * s + 2 + seqSize J))

def labF (N l : ℕ) : Fin (N + 1) := ⟨min l N, by omega⟩

def NN {s : ℕ} (J : List (Option (List (Fin s)))) : ℕ := 2 * s + 2 + seqSize J + s

def MM (s D : ℕ) (J : List (Option (List (Fin s)))) : Fin (NN J + 1) → St s D (Fin (NN J + 1)) :=
  fun x => progF (labF (NN J)) J x.val

theorem MM_lab (s D : ℕ) (J : List (Option (List (Fin s)))) (l : ℕ) (hl : l ≤ NN J) :
    MM s D J (labF (NN J) l) = progF (labF (NN J)) J l := by
  simp [MM, labF, Nat.min_eq_left hl]

theorem wholeRun (s D : ℕ) (J : List (Option (List (Fin s)))) (hJ : ∀ j ∈ J, jobOk D j)
    (t : List ℕ) :
    (adv (MM s D J))^[(encN t).length + (seqTime (fun j : Fin s => t.getD j.val 0) J +
        (∑ j ∈ Finset.range s, (vN (fun j : Fin s => t.getD j.val 0) j + 1) + 1))]
      (some ⟨some (labF (NN J) 0), none, stk (encN t) [] [] (fun _ => []) (fun _ => [])⟩) =
      some ⟨none, none,
        stk [] (seqOut (fun j : Fin s => t.getD j.val 0) J []) [] (fun _ => []) (fun _ => [])⟩ := by
  set val : Fin s → ℕ := fun j => t.getD j.val 0
  have hP : ∀ r, r < 2 * s + 2 → MM s D J (labF (NN J) r) = parseF (labF (NN J)) (2 * s + 2) r := by
    intro r hr
    rw [MM_lab s D J r (by unfold NN; omega), progF, if_pos hr]
  have hS : Loc (labF (NN J)) (MM s D J) (2 * s + 2) (seqSize J) (seqF (labF (NN J)) J (2 * s + 2)) := by
    intro r hr
    rw [MM_lab s D J _ (by unfold NN; omega), progF, if_neg (by omega), if_pos (by omega)]
    simp
  have hC : ∀ r, r < s + 1 → MM s D J (labF (NN J) (2 * s + 2 + seqSize J + r)) =
      cleanF (labF (NN J)) (2 * s + 2 + seqSize J) r := by
    intro r hr
    rw [MM_lab s D J _ (by unfold NN; omega), progF, if_neg (by omega), if_neg (by omega)]
    simp
  have h1 := parseSpec (labF (NN J)) (MM s D J) (2 * s + 2) hP (fun _ => []) t 0 (fun _ => []) (fun _ _ => rfl)
  have e1 : (fun j : Fin s => if j.val < 0 then ([] : List Bool) else rep (t.getD (j.val - 0) 0))
      = fun j => rep (val j) := by
    funext j; simp [val]
  rw [e1, show 2 * min 0 s = 0 by simp] at h1
  have h2 := seqSpec (labF (NN J)) (MM s D J) val (fun j => rep (val j)) (fun _ => rfl) J (2 * s + 2) [] hS hJ
  have h3 := cleanAll (labF (NN J)) (MM s D J) (2 * s + 2 + seqSize J) hC (seqOut val J []) (fun _ => []) val
    (fun j => rep (val j)) (fun _ => rfl) s le_rfl
  have e3 : (fun j : Fin s => if j.val < s then ([] : List Bool) else rep (val j)) = fun _ => [] := by
    funext j; simp
  rw [e3] at h3
  have h4 : adv (MM s D J) (some ⟨some (labF (NN J) (2 * s + 2 + seqSize J + s)), none,
      stk [] (seqOut val J []) [] (fun _ => []) (fun _ => [])⟩) =
      some ⟨none, none, stk [] (seqOut val J []) [] (fun _ => []) (fun _ => [])⟩ := by
    rw [adv_s, hC s (by omega), cleanF, dif_neg (by omega)]
    rfl
  exact itc h1 (itc h2 (itc h3 (it1 h4)))


theorem prod_flatMap' {α : Type} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).prod = (l.map (fun a => (f a).prod)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.prod_append, ih, List.map_cons, List.prod_cons]

theorem sum_flatMap' {α : Type} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]

noncomputable def monoL {s : ℕ} (m : Fin s →₀ ℕ) : List (Fin s) :=
  (List.finRange s).flatMap (fun i => List.replicate (m i) i)

noncomputable def msL {s : ℕ} (q : MvPolynomial (Fin s) ℕ) : List (List (Fin s)) :=
  q.support.toList.flatMap (fun m => List.replicate (q.coeff m) (monoL m))

noncomputable def jobsP {s : ℕ} (P : List (MvPolynomial (Fin s) ℕ)) :
    List (Option (List (Fin s))) :=
  none :: (P.reverse).flatMap (fun q => none :: some [] :: (msL q).map some)

theorem prod_monoL {s : ℕ} (val : Fin s → ℕ) (m : Fin s →₀ ℕ) :
    ((monoL m).map val).prod = ∏ i, val i ^ m i := by
  rw [monoL, List.map_flatMap, prod_flatMap', Fin.prod_univ_def]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [List.map_replicate, List.prod_replicate]

theorem eval_msL {s : ℕ} (val : Fin s → ℕ) (q : MvPolynomial (Fin s) ℕ) :
    MvPolynomial.eval val q = ((msL q).map (fun L => (L.map val).prod)).sum := by
  rw [MvPolynomial.eval_eq', msL, List.map_flatMap, sum_flatMap', ← Finset.sum_map_toList]
  congr 1
  apply List.map_congr_left
  intro m _
  rw [List.map_replicate, List.sum_replicate, smul_eq_mul, prod_monoL]

theorem seqOut_append {s : ℕ} (v : Fin s → ℕ) :
    ∀ (J1 J2 : List (Option (List (Fin s)))) (o : List Bool),
      seqOut v (J1 ++ J2) o = seqOut v J2 (seqOut v J1 o) := by
  intro J1
  induction J1 with
  | nil => intro J2 o; rfl
  | cons j J1 ih => intro J2 o; rw [List.cons_append, seqOut, seqOut, ih]

theorem seqOut_some {s : ℕ} (v : Fin s → ℕ) :
    ∀ (Ls : List (List (Fin s))) (o : List Bool),
      seqOut v (Ls.map some) o = rep ((Ls.map (fun L => (L.map v).prod)).sum) ++ o := by
  intro Ls
  induction Ls with
  | nil => intro o; rfl
  | cons L Ls ih =>
    intro o
    rw [List.map_cons, seqOut, ih, jobOut, List.map_cons, List.sum_cons, ← List.append_assoc,
      ← List.replicate_add, Nat.add_comm]

theorem rep_cons_comm (n : ℕ) (X : List Bool) : rep n ++ true :: X = true :: (rep n ++ X) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show true :: (rep n ++ true :: X) = true :: (true :: (rep n ++ X))
    rw [ih]

theorem seqOut_block {s : ℕ} (v : Fin s → ℕ) (q : MvPolynomial (Fin s) ℕ) (o : List Bool) :
    seqOut v (none :: some [] :: (msL q).map some) o =
      (true :: (List.replicate (MvPolynomial.eval v q) true ++ [false])) ++ o := by
  rw [seqOut, seqOut, seqOut_some, ← eval_msL, jobOut, jobOut]
  simp only [List.map_nil, List.prod_nil, List.replicate_one, List.singleton_append,
    List.cons_append, List.append_assoc]
  simp only [List.nil_append]
  exact rep_cons_comm _ _

theorem seqOut_blocks {s : ℕ} (v : Fin s → ℕ) :
    ∀ (Q : List (MvPolynomial (Fin s) ℕ)) (o : List Bool),
      seqOut v (Q.flatMap (fun q => none :: some [] :: (msL q).map some)) o =
        (Q.reverse.flatMap (fun q =>
          true :: (List.replicate (MvPolynomial.eval v q) true ++ [false]))) ++ o := by
  intro Q
  induction Q with
  | nil => intro o; rfl
  | cons q Q ih =>
    intro o
    rw [List.flatMap_cons, seqOut_append, seqOut_block, ih, List.reverse_cons,
      List.flatMap_append, List.append_assoc]
    simp

theorem seqOut_jobs {s : ℕ} (v : Fin s → ℕ) (P : List (MvPolynomial (Fin s) ℕ)) :
    seqOut v (jobsP P) [] = encN (P.map (fun q => MvPolynomial.eval v q)) := by
  rw [jobsP, seqOut, seqOut_blocks, List.reverse_reverse, encN,
    PEqualNP.CircuitLowerBounds.encodeList, List.flatMap_map]
  rfl


def jobLen {s : ℕ} : Option (List (Fin s)) → ℕ
  | none => 0
  | some L => L.length

def DD {s : ℕ} (J : List (Option (List (Fin s)))) : ℕ := (J.map jobLen).sum

theorem jobOk_DD {s : ℕ} (J : List (Option (List (Fin s)))) : ∀ j ∈ J, jobOk (DD J) j := by
  intro j hj
  have h : jobLen j ≤ DD J := List.le_sum_of_mem (List.mem_map_of_mem hj)
  cases j with
  | none => trivial
  | some L => simp only [jobOk]; simp only [jobLen] at h; omega

theorem getD_le : ∀ (t : List ℕ) (k : ℕ), t.getD k 0 ≤ (encN t).length := by
  intro t
  induction t with
  | nil => intro k; simp
  | cons a t ih =>
    intro k
    rw [encN_cons]
    cases k with
    | zero =>
      simp only [List.getD_cons_zero, List.length_cons, List.length_append, List.length_replicate]
      omega
    | succ k =>
      have := ih k
      simp only [List.getD_cons_succ, List.length_cons, List.length_append, List.length_replicate]
      omega

theorem monoTime_le {s : ℕ} (v : Fin s → ℕ) (n : ℕ) (hv : ∀ i, v i ≤ n) :
    ∀ L : List (Fin s), monoTime v L ≤ (3 * (n + 1)) ^ (L.length + 1) := by
  intro L
  induction L with
  | nil => simp [monoTime]; omega
  | cons i L ih =>
    rw [monoTime, List.length_cons, pow_succ _ (L.length + 1)]
    have hB : 3 * (n + 1) ≤ (3 * (n + 1)) ^ (L.length + 1) :=
      Nat.le_self_pow (by omega) _
    have h1 : v i * (monoTime v L + 1) ≤ n * ((3 * (n + 1)) ^ (L.length + 1) + 1) :=
      Nat.mul_le_mul (hv i) (by omega)
    have h2 := hv i
    nlinarith

theorem jobTime_le {s : ℕ} (v : Fin s → ℕ) (n Dm : ℕ) (hv : ∀ i, v i ≤ n)
    (j : Option (List (Fin s))) (hj : jobLen j ≤ Dm) :
    jobTime v j ≤ (3 * (n + 1)) ^ (Dm + 1) := by
  cases j with
  | none => simp only [jobTime]; exact Nat.one_le_pow _ _ (by omega)
  | some L =>
    simp only [jobTime]
    simp only [jobLen] at hj
    exact (monoTime_le v n hv L).trans (Nat.pow_le_pow_right (by omega) (by omega))

theorem seqTime_le {s : ℕ} (v : Fin s → ℕ) (B : ℕ) :
    ∀ J : List (Option (List (Fin s))), (∀ j ∈ J, jobTime v j ≤ B) →
      seqTime v J ≤ J.length * B := by
  intro J
  induction J with
  | nil => intro _; simp [seqTime]
  | cons j J ih =>
    intro h
    rw [seqTime, List.length_cons, Nat.succ_mul]
    have h1 := h j (by simp)
    have h2 := ih (fun j' hj' => h j' (by simp [hj']))
    omega

theorem clean_le {s : ℕ} (val : Fin s → ℕ) (n : ℕ) (hv : ∀ i, val i ≤ n) :
    ∑ j ∈ Finset.range s, (vN val j + 1) ≤ s * (n + 1) := by
  have : ∀ j ∈ Finset.range s, vN val j + 1 ≤ n + 1 := by
    intro j _
    unfold vN
    split_ifs with h
    · have := hv ⟨j, h⟩; omega
    · omega
  have h2 := Finset.sum_le_sum this
  simpa using h2

noncomputable def theTM (s D : ℕ) (J : List (Option (List (Fin s)))) : FinTM2 where
  K := KK s D
  k₀ := kI
  k₁ := kO
  Γ := fun _ => Bool
  Λ := Fin (NN J + 1)
  main := labF (NN J) 0
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := MM s D J

theorem init_eq (s D : ℕ) (J : List (Option (List (Fin s)))) (inp : List Bool) :
    initList (theTM s D J) inp =
      (⟨some (labF (NN J) 0), none, stk inp [] [] (fun _ => []) (fun _ => [])⟩ :
        Cf s D (Fin (NN J + 1))) := by
  unfold initList
  congr 1
  funext k
  rcases k with (_ | _) | (_ | (_ | _)) <;> rfl

theorem halt_eq (s D : ℕ) (J : List (Option (List (Fin s)))) (out : List Bool) :
    haltList (theTM s D J) out =
      (⟨none, none, stk [] out [] (fun _ => []) (fun _ => [])⟩ : Cf s D (Fin (NN J + 1))) := by
  unfold haltList
  congr 1
  funext k
  rcases k with (_ | _) | (_ | (_ | _)) <;> rfl

theorem wholeRun' (s : ℕ) (P : List (MvPolynomial (Fin s) ℕ)) (t : List ℕ) :
    (flip bind (theTM s (DD (jobsP P)) (jobsP P)).step)^[(encN t).length +
      (seqTime (fun j : Fin s => t.getD j.val 0) (jobsP P) +
        (∑ j ∈ Finset.range s, (vN (fun j : Fin s => t.getD j.val 0) j + 1) + 1))]
      (some (initList (theTM s (DD (jobsP P)) (jobsP P)) (encN t))) =
      Option.map (haltList (theTM s (DD (jobsP P)) (jobsP P)))
        (some (encN (P.map (fun q => MvPolynomial.eval (fun i : Fin s => t.getD i.val 0) q)))) := by
  show (adv (MM s (DD (jobsP P)) (jobsP P)))^[_] _ = some _
  rw [init_eq, halt_eq, ← seqOut_jobs]
  exact wholeRun s (DD (jobsP P)) (jobsP P) (jobOk_DD _) t

theorem total_le (n Sq Cl X A s : ℕ) (hA : n + 1 ≤ A) (hS : Sq ≤ X * A) (hC : Cl ≤ s * (n + 1)) :
    n + (Sq + (Cl + 1)) ≤ (2 + s + X) * A := by
  have h1 : s * (n + 1) ≤ s * A := Nat.mul_le_mul_left _ hA
  nlinarith

end PEqualNP.Outside.Meta507

theorem PEqualNP.Outside.L_meta_507 : ∀ (s : ℕ) (P : List (MvPolynomial (Fin s) ℕ)), PEqualNP.Library.ComputableInPolyTime (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false])) (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false])) (fun t : List ℕ => P.map (fun q : MvPolynomial (Fin s) ℕ => MvPolynomial.eval (fun i : Fin s => t.getD i.val 0) q)) := by
  intro s P
  open PEqualNP.Outside.Meta507 in
  exact ⟨{
    tm := theTM s (DD (jobsP P)) (jobsP P)
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := Polynomial.C (2 + s + (jobsP P).length * 3 ^ (DD (jobsP P) + 1)) *
      (Polynomial.X + 1) ^ (DD (jobsP P) + 1)
    outputsFun := fun t => {
      steps := (encN t).length + (seqTime (fun j : Fin s => t.getD j.val 0) (jobsP P) +
        (∑ j ∈ Finset.range s, (vN (fun j : Fin s => t.getD j.val 0) j + 1) + 1))
      evals_in_steps := by
        have hm : ∀ (l : List Bool), List.map (Equiv.refl Bool).invFun l = l :=
          fun l => by simp
        erw [hm, hm]
        exact wholeRun' s P t
      steps_le_m := by
        have hv : ∀ i : Fin s, t.getD i.val 0 ≤ (encN t).length := fun i => getD_le t i.val
        have hS := seqTime_le (fun j : Fin s => t.getD j.val 0) _ (jobsP P)
          (fun j hj => jobTime_le (fun j : Fin s => t.getD j.val 0) (encN t).length
            (DD (jobsP P)) hv j (List.le_sum_of_mem (List.mem_map_of_mem hj)))
        have hC := clean_le (fun j : Fin s => t.getD j.val 0) (encN t).length hv
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
        rw [mul_pow, ← Nat.mul_assoc] at hS
        refine total_le _ _ _ _ _ s ?_ hS hC
        calc (encN t).length + 1 = ((encN t).length + 1) ^ 1 := (pow_one _).symm
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega) } }⟩
