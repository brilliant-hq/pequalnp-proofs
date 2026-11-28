import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_33616 : (∀ (k r m q s d : Nat), 4 ≤ r → 2 ≤ q → 0 < s → k = q*s → s ≤ d → d < 2*s →
  let u := d-s
  let rot := fun (h w : Nat) =>
    ((w <<< (h % k)) ||| (w >>> (k - h % k))) % 2^k
  let step := fun (w : Nat) =>
    (List.range k).foldl (fun acc i => acc ||| ((xor (w.testBit i)
      (!(w.testBit ((i+1)%k)) && w.testBit ((i+2)%k))).toNat <<< i)) 0
  let state := fun (col : Bool) (w name : Nat) (c : Fin r → Fin (2^k)) =>
    let g := if col then 2 else 1
    (List.finRange r).foldl (fun x j =>
      step (x ^^^ rot g x ^^^ rot (k-g) x) ^^^
        rot (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
      (rot (if col then 3 else 1) w ^^^ name)
  let reach := fun col : Bool => if col then 7*r-2 else 5*r-3
  let delay := fun col : Bool => if col then 3*r+1 else 2*r-2
  let sign := fun b : Bool => if b then (-1 : ℤ) else 1
  let bits := fun (a x : Nat) => (List.range a).map (fun i => x.testBit i)
  let sched := fun (c : Fin r → Fin (2^k)) =>
    (List.finRange r).flatMap (fun j => bits k (c j).val)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (3*k+2*r*k+q+m*q+m+(k+1)) C ∧
    C.size ≤ 2^44*(k+r+m+5)^16*(2^(s-1+u)+2^(3*u)) ∧
    ∀ (nr nc : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (off : Fin k) (bank : Fin q → Bool),
      let p := fun i : Fin q => (off.val+i.val*s)%k
      let sensor := fun (i : Fin q) (w : Nat) =>
        (state (bank i) w (if bank i then nc.val else nr.val)
          (if bank i then cc else cr)).testBit ((p i + delay (bank i))%k)
      let valid := ∀ i, reach (bank i) ≤ d
      let K := fun (i : Fin q) (a b : Fin (2^u)) =>
        ∑ z : Fin (2^(s-1)),
          if z.val % 2^u = a.val then
            let h := fun (t : Bool) => sensor i (rot (p i)
              ((z.val <<< 1) ||| (t.toNat <<< s) ||| (b.val <<< (s+1))))
            if h false = h true then (0 : ℤ) else sign (h false)
          else 0
      let D := Matrix.trace ((List.ofFn
        (fun i : Fin q => (K i : Matrix (Fin (2^u)) (Fin (2^u)) ℤ))).prod)
      (valid → ∀ y : Fin q → Bool,
        ((Nat.card {w : Fin (2^k) // ∀ i, sensor i w.val = y i}) : ℤ) =
          (2 : ℤ)^(k-q) + sign ((List.ofFn y).foldl xor false) * D) ∧
      ∀ (A : Fin m → Fin (2^q)) (v : Fin m → Bool) (t : Fin (2^(k+1))),
        let obs := fun (w : Nat) (j : Fin m) => (List.finRange q).foldl
          (fun b i => xor b ((A j).val.testBit i.val && sensor i w)) false
        let hits := Nat.card {w : Fin (2^k) // ∀ j, obs w.val j = v j}
        let masks := (List.finRange m).flatMap (fun j => bits q (A j).val)
        C.eval (bits k nr.val ++ bits k nc.val ++ sched cr ++ sched cc ++ bits k off.val ++
          List.ofFn bank ++ masks ++ List.ofFn v ++ bits (k+1) t.val) =
            decide (valid ∧ t.val ≤ hits)) := by
    classical
    first
    | exact?
    | intro k r m q s d hr hq hs hk hsd hd
      have h₂ : 2 * s ≤ k := by
        rw [hk]
        exact Nat.mul_le_mul_right s hq
      have hk₀ : 0 < k := by omega
      have hdk : d < k := by omega
      have hu : d - s < s := by omega
      have hsplit : s + (d - s) = d := by omega
      have combine {T I J O B : Type} {F R S : T → Prop}
          {P : I → I → J → J → O → B → Prop}
          {Q : T → I → I → J → J → O → B → Prop}
          (hp : ∀ i j a b o v, P i j a b o v)
          (hc : (∀ i j a b o v, P i j a b o v) →
            ∃ t, F t ∧ R t ∧ S t ∧ ∀ i j a b o v, Q t i j a b o v) :
          ∃ t, F t ∧ R t ∧ S t ∧ ∀ i j a b o v, P i j a b o v ∧ Q t i j a b o v := by
        obtain ⟨t, hf, hr', hs', ht⟩ := hc hp
        exact ⟨t, hf, hr', hs', fun i j a b o v => ⟨hp i j a b o v, ht i j a b o v⟩⟩
      first
      | exact?
      | apply? <;> (first | assumption | omega | exact?)
      | apply combine
        all_goals
          intros
          first
          | exact?
          | apply? <;> (first | assumption | omega | exact?)
      | subst k
        obtain ⟨a, ha, rfl⟩ : ∃ a : Nat, a < s ∧ d = s + a :=
          ⟨d - s, hu, hsplit.symm⟩
        have hsub : s + a - s = a := by omega
        simp only [hsub]
        first
        | exact?
        | apply? <;> (first | assumption | omega | exact?)
        | apply combine
          all_goals
            intros
            first
            | exact?
            | apply? <;> (first | assumption | omega | exact? | grind)
