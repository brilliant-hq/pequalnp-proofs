import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7782_4
    (h1 : let adj (i : Fin 12) (j : Fin 9) : Bool := decide (i.val % 3 =
          if i.val / 3 = 3 then j.val / 3 else (j.val % 3 + (i.val / 3) * (j.val / 3)) % 3)
        ∃ (gs : List (Bool × ℕ × ℕ)) (o : ℕ), gs.length ≤ 43 ∧
          let ev (r : Fin 12 → Bool) (c : Fin 9 → Bool) :=
            (gs.foldl (fun w g => w ++ [if g.1 then w.getD g.2.1 (r 0) || w.getD g.2.2 (r 0)
                else w.getD g.2.1 (r 0) && w.getD g.2.2 (r 0)]) (List.ofFn r ++ List.ofFn c)).getD o (r 0)
          (∀ i j, adj i j = true → ev (fun k => decide (k = i)) (fun k => decide (k = j)) = true) ∧
          ∀ c : Fin 9 → Bool, ev (fun i => decide (∀ j, c j = true → adj i j = false)) c = false)
    (h2 : let adj (i : Fin 12) (j : Fin 9) : Bool := decide (i.val % 3 =
          if i.val / 3 = 3 then j.val / 3 else (j.val % 3 + (i.val / 3) * (j.val / 3)) % 3)
        ∃ (row : Fin 12 → Fin 13) (col : Fin 9 → Fin 13), ∀ p l,
          (l.val ∉ ([0,1,3,9] : List ℕ) ∧ (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ)) ↔
          ∃ i j, row i = p ∧ col j = l ∧ adj i j = true) : have x1 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map (fun (x1 : (Fin (26 : ℕ) → Bool) → Bool) (x2 : Bool) => {x3 : Fin (26 : ℕ) → Bool | x1 x3 = x2}) ((List.ofFn fun (x1 : Fin (26 : ℕ)) (x2 : Fin (26 : ℕ) → Bool) => x2 x1) ++ [fun (x1 : Fin (26 : ℕ) → Bool) => x1 (0 : Fin (26 : ℕ)) || x1 (1 : Fin (26 : ℕ))]); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), ↑x4 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ (x3 : List (Bool → Set (Fin (26 : ℕ) → Bool))) (x4 : Bool → Set (Fin (26 : ℕ) → Bool)),   x3.length ≤ (43 : ℕ) ∧     x4 ∈ x1 ++ x3 ∧       (∀ (x5 : Fin x3.length),           have x6 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := x1 ++ List.take (↑x5) x3;           ∃ x7 ∈ x6, ∃ x8 ∈ x6, ∃ (x9 : Bool), ∀ (x10 : Bool), x3.get x5 x10 ⊆ if x10 = x9 then x7 x10 ∪ x8 x10 else x7 x10 ∩ x8 x10) ∧         ∀ (x5 : Fin (26 : ℕ) → Bool), (x2 x5 → x5 ∈ x4 Bool.true) ∧ (¬x2 x5 → x5 ∈ x4 Bool.false) := by
  let X := Fin 26 → Bool
  let F := X → Bool
  let W := Bool → Set X
  let Code := Bool × ℕ × ℕ
  let bin (op a b : Bool) := if op then a || b else a && b
  let step (d : Bool) (w : List Bool) (g : Code) :=
    w ++ [bin g.1 (w.getD g.2.1 d) (w.getD g.2.2 d)]
  let ev (gs : List Code) (o : ℕ) (r : Fin 12 → Bool) (c : Fin 9 → Bool) :=
    (gs.foldl (step (r 0)) (List.ofFn r ++ List.ofFn c)).getD o (r 0)
  let adj (i : Fin 12) (j : Fin 9) : Bool := decide (i.val % 3 =
    if i.val / 3 = 3 then j.val / 3 else (j.val % 3 + (i.val / 3) * (j.val / 3)) % 3)
  let Good (gs : List Code) (o : ℕ) :=
    (∀ i j, adj i j = true → ev gs o (fun k => decide (k = i)) (fun k => decide (k = j)) = true) ∧
    ∀ c : Fin 9 → Bool, ev gs o (fun i => decide (∀ j, c j = true → adj i j = false)) c = false
  let tag (f : F) (b : Bool) : Set X := {x | f x = b}
  let Legal (a t : List W) := ∀ i : Fin t.length,
    let s := a ++ t.take i.val
    ∃ u ∈ s, ∃ v ∈ s, ∃ op : Bool, ∀ b, t.get i b ⊆ if b = op then u b ∪ v b else u b ∩ v b
  have tag_bin (op : Bool) (f g : F) (b : Bool) :
      tag (fun x => bin op (f x) (g x)) b ⊆
      if b = op then tag f b ∪ tag g b else tag f b ∩ tag g b := by
    cases op <;> cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false] <;>
      intro x hx <;> cases hf : f x <;> cases hg : g x <;>
      simp [tag, bin, hf, hg] at hx ⊢
  have read_mem (d : F) (w : List F) (a : List W) (hd : tag d ∈ a)
      (hw : ∀ f ∈ w, tag f ∈ a) (k : ℕ) : tag (w.getD k d) ∈ a := by
    by_cases hk : k < w.length
    · rw [List.getD_eq_getElem w d hk]; exact hw _ (List.getElem_mem hk)
    · rwa [List.getD_eq_default w d (by omega)]
  have compile (gs : List Code) (o : ℕ) (d : F) (w : List F) (a : List W)
      (hd : tag d ∈ a) (hw : ∀ f ∈ w, tag f ∈ a) :
      ∃ t : List W, t.length = gs.length ∧ Legal a t ∧
        tag (fun x => (gs.foldl (step (d x)) (w.map (fun f => f x))).getD o (d x)) ∈ a ++ t := by
    induction gs generalizing w a with
    | nil => exact ⟨[], rfl, fun i => Fin.elim0 i, by simpa [List.getD_map] using read_mem d w a hd hw o⟩
    | cons g gs ih =>
      let u := w.getD g.2.1 d
      let v := w.getD g.2.2 d
      let f : F := fun x => bin g.1 (u x) (v x)
      have hmem {z} (hz : z ∈ a) : z ∈ a ++ [tag f] := List.mem_append_left _ hz
      obtain ⟨t,hl,ht,ho⟩ := ih (w ++ [f]) (a ++ [tag f]) (hmem hd) (by
        intro z hz
        rcases List.mem_append.mp hz with h|h
        · exact hmem (hw z h)
        · rw [List.mem_singleton.mp h]; exact List.mem_append_right _ (by simp))
      refine ⟨tag f :: t, by simp [hl], ?_, ?_⟩
      · rintro ⟨k,hk⟩
        cases k with
        | zero =>
          simp only [List.take_zero, List.append_nil]
          exact (show ∃ u' ∈ a, ∃ v' ∈ a, ∃ op : Bool, ∀ b,
            tag f b ⊆ if b = op then u' b ∪ v' b else u' b ∩ v' b from
            ⟨tag u, read_mem d w a hd hw _, tag v, read_mem d w a hd hw _, g.1, tag_bin g.1 u v⟩)
        | succ k =>
          simpa [List.append_assoc] using ht ⟨k,by simpa using hk⟩
      · simpa only [List.foldl_cons,List.map_append,List.map_singleton,List.append_assoc,
          List.singleton_append,step,List.getD_map,f,u,v] using ho
  let impB (a b : Bool) := a = true → b = true
  have mono_eval (gs : List Code) (o : ℕ) {r r' : Fin 12 → Bool} {c c' : Fin 9 → Bool}
      (hr : ∀ i, impB (r i) (r' i)) (hc : ∀ j, impB (c j) (c' j)) :
      impB (ev gs o r c) (ev gs o r' c') := by
    have get {l l' : List Bool} (h : List.Forall₂ impB l l') (n : ℕ) :
        impB (l.getD n (r 0)) (l'.getD n (r' 0)) := by
      induction h generalizing n with
      | nil => simpa using hr 0
      | cons h _ ih => cases n <;> first | exact h | apply ih
    have cat {l l' t t' : List Bool} (h : List.Forall₂ impB l l') (k : List.Forall₂ impB t t') :
        List.Forall₂ impB (l++t) (l'++t') := by
      induction h with
      | nil => exact k
      | cons h _ ih => exact .cons h ih
    have fold {l l' : List Bool} (h : List.Forall₂ impB l l') :
        List.Forall₂ impB (gs.foldl (step (r 0)) l) (gs.foldl (step (r' 0)) l') := by
      induction gs generalizing l l' with
      | nil => exact h
      | cons g gs ih =>
        apply ih; apply cat h; apply List.Forall₂.cons _ .nil
        have h₁ := get h g.2.1
        have h₂ := get h g.2.2
        cases g.1 <;> simp only [bin,impB,Bool.false_eq_true,ite_false,ite_true,Bool.and_eq_true,Bool.or_eq_true]
        · exact And.imp h₁ h₂
        · exact Or.imp h₁ h₂
    have lift {n : ℕ} {a b : Fin n → Bool} (h : ∀ i, impB (a i) (b i)) :
        List.Forall₂ impB (List.ofFn a) (List.ofFn b) := by
      apply List.forall₂_of_length_eq_of_get (by simp)
      intro i h₁ h₂
      simpa only [List.get_eq_getElem, List.getElem_ofFn] using h ⟨i,by simpa using h₁⟩
    exact get (fold (cat (lift hr) (lift hc))) o
  have tests_exact (gs : List Code) (o : ℕ) (h : Good gs o) (r : Fin 12 → Bool) (c : Fin 9 → Bool) :
      ev gs o r c = true ↔ ∃ i j, adj i j = true ∧ r i = true ∧ c j = true := by
    constructor
    · intro hx
      by_contra no
      have m (i) : impB (r i) (decide (∀ j, c j = true → adj i j = false)) := by
        intro hi
        apply decide_eq_true
        intro j hj
        cases ha : adj i j
        · rfl
        · exact False.elim (no ⟨i,j,ha,hi,hj⟩)
      have := mono_eval gs o m (fun _ => id) hx
      rw [h.2 c] at this
      contradiction
    · rintro ⟨i,j,ha,hi,hj⟩
      apply @mono_eval gs o (fun k => decide (k = i)) r (fun k => decide (k = j)) c _ _ (h.1 i j ha)
      · intro k hk; simpa [of_decide_eq_true hk] using hi
      · intro k hk; simpa [of_decide_eq_true hk] using hj
  let old (p l : Fin 13) := l.val ∉ ([0,1,3,9] : List ℕ) ∧ (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ)
  let Coord (row : Fin 12 → Fin 13) (col : Fin 9 → Fin 13) := ∀ p l,
    old p l ↔ ∃ i j, row i = p ∧ col j = l ∧ adj i j = true
  let start := (List.ofFn (fun k : Fin 26 => fun x : X => x k) ++ [fun x : X => x 0 || x 1]).map tag
  let flag (x : X) := ∃ p l, old p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  let result (n : ℕ) := ∃ (t : List W) (v : W), t.length ≤ n ∧ v ∈ start ++ t ∧ Legal start t ∧
    ∀ x, (flag x → x ∈ v true) ∧ (¬flag x → x ∈ v false)
  have assemble (n : ℕ) (hs : ∃ gs o, List.length gs ≤ n ∧ Good gs o)
      (hg : ∃ r c, Coord r c) : result n := by
    obtain ⟨gs,o,hn,hgates⟩ := hs
    obtain ⟨row,col,hcoord⟩ := hg
    let R (i : Fin 12) (x : X) := x (Fin.castAdd 13 (row i))
    let C (j : Fin 9) (x : X) := x (Fin.natAdd 13 (col j))
    let ws := List.ofFn R ++ List.ofFn C
    have raw (k : Fin 26) : tag (fun x => x k) ∈ start :=
      List.mem_map.mpr ⟨_,List.mem_append_left _ (List.mem_ofFn.mpr ⟨k,rfl⟩),rfl⟩
    have hw : ∀ f ∈ ws, tag f ∈ start := by
      intro f hf
      rcases List.mem_append.mp hf with h|h <;> obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h <;> exact raw _
    obtain ⟨t,ht,hl,hm⟩ := compile gs o (R 0) ws start (raw _) hw
    let v : F := fun x => ev gs o (fun i => R i x) (fun j => C j x)
    have hmap (x : X) : ws.map (fun f => f x) = List.ofFn (fun i => R i x) ++ List.ofFn (fun j => C j x) := by
      simp only [ws,List.map_append,List.map_ofFn,Function.comp_def]
    refine ⟨t,tag v,ht ▸ hn,?_,hl,?_⟩
    · have e : (fun x => (gs.foldl (step (R 0 x)) (ws.map (fun f => f x))).getD o (R 0 x)) = v := by
        funext x
        rw [hmap x]
      exact e ▸ hm
    · intro x
      have he : v x = true ↔ flag x := by
        apply (tests_exact gs o hgates (fun i => R i x) (fun j => C j x)).trans
        constructor
        · rintro ⟨i,j,ha,hr,hc⟩
          exact ⟨_,_,(hcoord _ _).mpr ⟨_,_,rfl,rfl,ha⟩,hr,hc⟩
        · rintro ⟨p,l,hp,hr,hc⟩
          obtain ⟨i,j,rfl,rfl,ha⟩ := (hcoord _ _).mp hp
          exact ⟨_,_,ha,hr,hc⟩
      exact ⟨he.mpr, fun hn => Bool.eq_false_iff.mpr (fun h => hn (he.mp h))⟩
  simpa only [result, flag, old, and_assoc, start, tag, Legal] using assemble 43 h1 h2
