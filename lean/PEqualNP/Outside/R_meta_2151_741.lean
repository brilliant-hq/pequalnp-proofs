import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2151_741
    (hTail : ∀ (g : Gate) (G : List Gate) (o : ℕ) (x : Fin 9 → Bool),
      let C : Circuit := ⟨g :: G, o⟩
      let R : Circuit := ⟨G, o⟩
      (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4) →
      circuitFun 9 C x = R.eval (List.ofFn x ++ [x 0 || x 4]))
    (hTable : ∀ x : Fin 9 → Bool,
      ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hFind : ∀ R : Circuit, FanInTwo R → R.size ≤ 14 →
      Option.map (fun g : Gate => g.op) R.gates[0]? = some GateOp.or →
      ∃ m : Fin 512,
        let x := fun i : Fin 9 => decide ((m.val / (2 ^ (i.val % 9) : ℕ)) % 2 = 1)
        R.eval (List.ofFn x ++ [x 0 || x 4]) ≠ ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (16 : ℕ) ≤ x1.size := by
  intro C hFan hFirst hFunction hSecond
  by_contra! hSmall
  obtain ⟨G, o⟩ := C
  cases G with
  | nil => simp at hSecond
  | cons g G =>
    let R : Circuit := ⟨G, o⟩
    have hFanR : FanInTwo R := by
      intro k hk
      exact hFan k (List.mem_cons_of_mem g hk)
    have hSizeR : R.size ≤ 14 := by
      change G.length + 1 < 16 at hSmall
      change G.length ≤ 14
      omega
    have hFirstR : Option.map (fun k : Gate => k.op) R.gates[0]? = some GateOp.or := hSecond
    obtain ⟨m, hm⟩ := hFind R hFanR hSizeR hFirstR
    let x : Fin 9 → Bool := fun i => decide ((m.val / (2 ^ (i.val % 9) : ℕ)) % 2 = 1)
    change R.eval (List.ofFn x ++ [x 0 || x 4]) ≠ ([(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) at hm
    rw [hTable x, ← hTail g G o x (hFirst x)] at hm
    exact hm (congrFun hFunction x)
