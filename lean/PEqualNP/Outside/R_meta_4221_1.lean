import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4221_1
    (h_len1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (a : ℕ),
      PEqualNP.MetaComplexity.Monotone2 x1 → (26 : ℕ) ≤ a → a < (26 : ℕ) + x1.size →
      (let x6 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x6 x7 : Fin (13 : ℕ)) => (↑x6 + ↑x7) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
        have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Fin (26 : ℕ)) => if ↑x9 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x7) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x8);
        have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x8 : Finset (Fin (13 : ℕ))) => {x9 : Fin (13 : ℕ) | ∀ x10 ∈ x8, ¬x6 x10 x9};
        have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => (x1.wires (List.ofFn (x7 x9 x10))).getD a Bool.false;
        (∀ (x10 x11 : Fin (13 : ℕ)), x6 x10 x11 → x9 {x10} {x11} = Bool.true) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x9 x10 (x8 x10) = Bool.false ∧ x9 (x8 x10) x10 = Bool.false) →
      (63 : ℕ) ≤ x1.size)
    (h_len2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
      PEqualNP.MetaComplexity.Monotone2 x1 → ((26 : ℕ) ≤ a ∨ (26 : ℕ) ≤ b) → a < (26 : ℕ) + x1.size → b < (26 : ℕ) + x1.size →
      (let x6 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x6 x7 : Fin (13 : ℕ)) => (↑x6 + ↑x7) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
        have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Fin (26 : ℕ)) => if ↑x9 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x7) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x8);
        have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x8 : Finset (Fin (13 : ℕ))) => {x9 : Fin (13 : ℕ) | ∀ x10 ∈ x8, ¬x6 x10 x9};
        have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => (x1.wires (List.ofFn (x7 x9 x10))).getD a Bool.false && (x1.wires (List.ofFn (x7 x9 x10))).getD b Bool.false;
        (∀ (x10 x11 : Fin (13 : ℕ)), x6 x10 x11 → x9 {x10} {x11} = Bool.true) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x9 x10 (x8 x10) = Bool.false ∧ x9 (x8 x10) x10 = Bool.false) →
      (63 : ℕ) ≤ x1.size)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (∃ x5 ∈ x2, (26 : ℕ) ≤ x5) →         (let x6 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x6 x7 : Fin (13 : ℕ)) => (↑x6 + ↑x7) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];           have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Fin (26 : ℕ)) => if ↑x9 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x7) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x8);           have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x8 : Finset (Fin (13 : ℕ))) => {x9 : Fin (13 : ℕ) | ∀ x10 ∈ x8, ¬x6 x10 x9};           have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x11 : ℕ) => (x1.wires (List.ofFn (x7 x9 x10))).getD x11 Bool.false) x2);           (∀ (x10 x11 : Fin (13 : ℕ)), x6 x10 x11 → x9 {x10} {x11} = Bool.true) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x9 x10 (x8 x10) = Bool.false ∧ x9 (x8 x10) x10 = Bool.false) →           (63 : ℕ) ≤ x1.size := by
  intro x1 x2 hm hlen hge hspec
  have h_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
    intro gs; induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]; omega
  have and_eval_all : ∀ (bs : List Bool), PEqualNP.CircuitLowerBounds.GateOp.and.eval bs = true → ∀ b ∈ bs, b = true := by
    intro bs
    induction bs with
    | nil => simp
    | cons b bs ih =>
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, Bool.and_eq_true, List.mem_cons]
      intro ⟨hb, hbs⟩ x hx
      rcases hx with rfl | hx
      · exact hb
      · exact ih hbs x hx
  have h_lt : ∀ w ∈ x2, w < 26 + x1.size := by
    intro w hw
    by_contra hge_w
    have hge_w' : 26 + x1.size ≤ w := Nat.le_of_not_lt hge_w
    have h00 : ((0 : Fin 13).val + (0 : Fin 13).val) % 13 ∈ [0, 1, 3, 9] := by decide
    have hpos := hspec.1 0 0 h00
    dsimp only at hpos
    have hmem : (x1.wires (List.ofFn (fun x9 : Fin 26 => if ↑x9 < 13 then decide (Fin.ofNat 13 ↑x9 ∈ ({0} : Finset (Fin 13))) else decide (Fin.ofNat 13 ↑x9 ∈ ({0} : Finset (Fin 13)))))).getD w false = true :=
      and_eval_all _ hpos _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
    have hlen_w : (x1.wires (List.ofFn (fun x9 : Fin 26 => if ↑x9 < 13 then decide (Fin.ofNat 13 ↑x9 ∈ ({0} : Finset (Fin 13))) else decide (Fin.ofNat 13 ↑x9 ∈ ({0} : Finset (Fin 13)))))).length = 26 + x1.size := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, h_len, List.length_ofFn]; rfl
    have hdef : (x1.wires (List.ofFn (fun x9 : Fin 26 => if ↑x9 < 13 then decide (Fin.ofNat 13 ↑x9 ∈ ({0} : Finset (Fin 13))) else decide (Fin.ofNat 13 ↑x9 ∈ ({0} : Finset (Fin 13)))))).getD w false = false :=
      List.getD_eq_default _ _ (hlen_w ▸ hge_w')
    rw [hdef] at hmem
    exact Bool.noConfusion hmem
  rcases x2 with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hge with ⟨w, hw, _⟩; exact absurd hw (by simp)
  · rcases hge with ⟨w, hw, hw26⟩
    simp only [List.mem_singleton] at hw
    subst hw
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true] at hspec
    exact h_len1 x1 w hm hw26 (h_lt w (by simp)) hspec
  · have ha_lt := h_lt a (by simp)
    have hb_lt := h_lt b (by simp)
    have hab26 : 26 ≤ a ∨ 26 ≤ b := by
      rcases hge with ⟨w, hw, hw26⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> [exact Or.inl hw26; exact Or.inr hw26]
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true] at hspec
    exact h_len2 x1 a b hm hab26 ha_lt hb_lt hspec
  · simp at hlen
