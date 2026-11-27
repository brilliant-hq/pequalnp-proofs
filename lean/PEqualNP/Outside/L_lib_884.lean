import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_884_aux

open Classical

private lemma main_proof :
∀ (q k : Nat), 2 ≤ q →
  let V := Option (Fin q) × Bool
  ∀ name : V ↪ Fin k,
  let hub := fun b : Bool => name (none,b)
  let leaf := fun (c : Fin q) (b : Bool) => name (some c,b)
  let star := fun b : Bool => insert (hub b) (Finset.univ.image (fun c : Fin q => leaf c b))
  let neutral := fun S : Finset (Fin k) => ∃ c, leaf c false ∈ S ∧ leaf c true ∈ S
  let desired := fun (c : Fin q) (S : Finset (Fin k)) =>
    (∃ b, hub b ∈ S ∧ leaf c b ∈ S) ∨
    (∃ j, j ≠ c ∧ leaf j false ∈ S ∧ leaf j true ∈ S)
  (∀ P : Equiv.Perm (Fin k), Function.Involutive P →
    let hit := fun S : Finset (Fin k) => ∃ u ∈ S, P u ∈ S ∧ P u ≠ u
    let chosen := fun c : Fin q =>
      (∀ b, P (hub b) = leaf c b) ∧
      ∀ j, j ≠ c → P (leaf j false) = leaf j true
    ((∀ (c : Fin q) (b : Bool), hit {hub b, leaf c false, leaf c true}) ∧ hit (star false)) ↔
      ∃! c, chosen c) ∧
  ∀ S : Finset (Fin k), S.card ≤ q+1 →
    ((¬ neutral S ∧ ∀ c, desired c S) ↔ S = star false ∨ S = star true) := by
  intro q k hq V name hub leaf star neutral desired
  have hub_ne_leaf : ∀ (b : Bool) (c : Fin q) (b' : Bool), hub b ≠ leaf c b' := by
    intro b c b' h
    have h1 : (none : Option (Fin q)) = some c := congrArg Prod.fst (name.injective h)
    cases h1
  have hub_inj : ∀ {b1 b2 : Bool}, hub b1 = hub b2 → b1 = b2 := by
    intro b1 b2 h
    exact congrArg Prod.snd (name.injective h)
  have leaf_inj : ∀ {c1 c2 : Fin q} {b1 b2 : Bool}, leaf c1 b1 = leaf c2 b2 → c1 = c2 ∧ b1 = b2 := by
    intro c1 c2 b1 b2 h
    have h' := name.injective h
    exact ⟨Option.some.inj (congrArg Prod.fst h'), congrArg Prod.snd h'⟩
  have hub_ft : hub false ≠ hub true := fun h => by
    have := hub_inj h
    simp at this
  have leaf_ft : ∀ c : Fin q, leaf c false ≠ leaf c true := fun c h => by
    have := (leaf_inj h).2
    simp at this
  have hstar_card : ∀ b : Bool, (star b).card = q + 1 := by
    intro b
    have hnot : hub b ∉ Finset.univ.image (fun c : Fin q => leaf c b) := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro c hc
      exact (hub_ne_leaf b c b) hc.symm
    have hinj : Function.Injective (fun c : Fin q => leaf c b) := fun c1 c2 h => (leaf_inj h).1
    dsimp only [star]
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hinj, Finset.card_fin]
  constructor
  · intro P hP hit chosen
    have htri : ∀ (x y z : Fin k), x ≠ y → x ≠ z → y ≠ z →
        (hit ({x, y, z} : Finset (Fin k)) ↔ P x = y ∨ P x = z ∨ P y = z) := by
      intro x y z hxy hxz hyz
      constructor
      · rintro ⟨u, hu, hPu, hne⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hPu
        rcases hu with rfl | rfl | rfl
        · rcases hPu with h1 | h1 | h1
          · exact absurd h1 hne
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1)
        · rcases hPu with h1 | h1 | h1
          · left; rw [← h1, hP u]
          · exact absurd h1 hne
          · exact Or.inr (Or.inr h1)
        · rcases hPu with h1 | h1 | h1
          · right; left; rw [← h1, hP u]
          · right; right; rw [← h1, hP u]
          · exact absurd h1 hne
      · rintro (h | h | h)
        · refine ⟨x, by simp, ?_, ?_⟩
          · rw [h]; simp
          · rw [h]; exact hxy.symm
        · refine ⟨x, by simp, ?_, ?_⟩
          · rw [h]; simp
          · rw [h]; exact hxz.symm
        · refine ⟨y, by simp, ?_, ?_⟩
          · rw [h]; simp
          · rw [h]; exact hyz.symm
    constructor
    · rintro ⟨htris, hstar⟩
      have htri_apply : ∀ (c : Fin q) (b : Bool),
          P (hub b) = leaf c false ∨ P (hub b) = leaf c true ∨ P (leaf c false) = leaf c true := by
        intro c b
        exact (htri (hub b) (leaf c false) (leaf c true)
          (hub_ne_leaf b c false) (hub_ne_leaf b c true) (leaf_ft c)).mp (htris c b)
      have huniq_bad : ∀ c1 c2 : Fin q,
          P (leaf c1 false) ≠ leaf c1 true → P (leaf c2 false) ≠ leaf c2 true → c1 = c2 := by
        intro c1 c2 h1 h2
        have h1' : P (hub false) = leaf c1 false ∨ P (hub false) = leaf c1 true := by
          rcases htri_apply c1 false with a | a | a
          · exact Or.inl a
          · exact Or.inr a
          · exact absurd a h1
        have h2' : P (hub false) = leaf c2 false ∨ P (hub false) = leaf c2 true := by
          rcases htri_apply c2 false with a | a | a
          · exact Or.inl a
          · exact Or.inr a
          · exact absurd a h2
        rcases h1' with h1' | h1' <;> rcases h2' with h2' | h2'
        · exact (leaf_inj (h1'.symm.trans h2')).1
        · exact (leaf_inj (h1'.symm.trans h2')).1
        · exact (leaf_inj (h1'.symm.trans h2')).1
        · exact (leaf_inj (h1'.symm.trans h2')).1
      have hmem_star : ∀ u : Fin k, u ∈ star false ↔ u = hub false ∨ ∃ c : Fin q, u = leaf c false := by
        intro u
        simp only [star, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, eq_comm]
      have hex_c0 : ∃ c0 : Fin q, P (hub false) = leaf c0 false := by
        rcases hstar with ⟨u, hu, hPu, hne⟩
        rw [hmem_star] at hu hPu
        rcases hu with rfl | ⟨c1, rfl⟩
        · rcases hPu with h1 | ⟨c0, h1⟩
          · exact absurd h1 hne
          · exact ⟨c0, h1⟩
        · rcases hPu with h1 | ⟨c2, h1⟩
          · refine ⟨c1, ?_⟩
            rw [← h1, hP (leaf c1 false)]
          · exfalso
            have hc12 : c1 ≠ c2 := fun heq => hne (by rw [h1, heq])
            have hbad1 : P (leaf c1 false) ≠ leaf c1 true := by
              rw [h1]; intro h; exact by have := (leaf_inj h).2; simp at this
            have hbad2 : P (leaf c2 false) ≠ leaf c2 true := by
              have hP2 : P (leaf c2 false) = leaf c1 false := by rw [← h1, hP (leaf c1 false)]
              rw [hP2]; intro h; exact by have := (leaf_inj h).2; simp at this
            exact hc12 (huniq_bad c1 c2 hbad1 hbad2)
      rcases hex_c0 with ⟨c0, hc0⟩
      refine ⟨c0, ?_, ?_⟩
      · constructor
        · intro b
          cases b
          · exact hc0
          · rcases htri_apply c0 true with h1 | h1 | h1
            · exfalso
              have := P.injective (h1.trans hc0.symm)
              exact hub_ft this.symm
            · exact h1
            · exfalso
              have h2 : P (leaf c0 false) = hub false := by rw [← hc0, hP (hub false)]
              exact (hub_ne_leaf false c0 true) (h2.symm.trans h1)
        · intro j hj
          rcases htri_apply j false with h1 | h1 | h1
          · exfalso; exact hj ((leaf_inj (hc0.symm.trans h1)).1.symm)
          · exfalso; exact hj ((leaf_inj (hc0.symm.trans h1)).1.symm)
          · exact h1
      · intro c hc
        have heq : leaf c false = leaf c0 false := (hc.1 false).symm.trans hc0
        exact (leaf_inj heq).1
    · rintro ⟨c0, ⟨hhub, hleaf⟩, _⟩
      constructor
      · intro c b
        rw [htri (hub b) (leaf c false) (leaf c true)
          (hub_ne_leaf b c false) (hub_ne_leaf b c true) (leaf_ft c)]
        by_cases hcc0 : c = c0
        · subst hcc0
          cases b
          · exact Or.inl (hhub false)
          · exact Or.inr (Or.inl (hhub true))
        · exact Or.inr (Or.inr (hleaf c hcc0))
      · refine ⟨hub false, Finset.mem_insert_self _ _, ?_, ?_⟩
        · rw [hhub false]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ c0))
        · rw [hhub false]
          exact (hub_ne_leaf false c0 false).symm
  · intro S hScard
    constructor
    · rintro ⟨hneut, hdes⟩
      have hall : ∀ c : Fin q, ∃ b : Bool, hub b ∈ S ∧ leaf c b ∈ S := by
        intro c
        rcases hdes c with h1 | ⟨j, _, hf, ht⟩
        · exact h1
        · exact absurd ⟨j, hf, ht⟩ hneut
      let hb : Fin q → Bool := fun c => Classical.choose (hall c)
      have hhb : ∀ c : Fin q, hub (hb c) ∈ S ∧ leaf c (hb c) ∈ S :=
        fun c => Classical.choose_spec (hall c)
      let L : Finset (Fin k) := Finset.univ.image (fun c : Fin q => leaf c (hb c))
      have hL_sub : L ⊆ S := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨c, _, rfl⟩
        exact (hhb c).2
      have hL_card : L.card = q := by
        have hinj : Function.Injective (fun c : Fin q => leaf c (hb c)) := fun c1 c2 h => (leaf_inj h).1
        rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
      have hhub_notL : ∀ b : Bool, hub b ∉ L := by
        intro b hmem
        rcases Finset.mem_image.mp hmem with ⟨c, _, hc⟩
        exact (hub_ne_leaf b c (hb c)) hc.symm
      have hnot_both : ¬ (hub false ∈ S ∧ hub true ∈ S) := by
        rintro ⟨hf, ht⟩
        have hsub : insert (hub false) (insert (hub true) L) ⊆ S := by
          intro x hx
          simp only [Finset.mem_insert] at hx
          rcases hx with rfl | rfl | hxL
          · exact hf
          · exact ht
          · exact hL_sub hxL
        have hnot1 : hub false ∉ insert (hub true) L := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨hub_ft, hhub_notL false⟩
        have hcard2 : (insert (hub false) (insert (hub true) L)).card = q + 2 := by
          rw [Finset.card_insert_of_notMem hnot1, Finset.card_insert_of_notMem (hhub_notL true), hL_card]
        have hle := Finset.card_le_card hsub
        omega
      let c0 : Fin q := ⟨0, by omega⟩
      let b0 : Bool := hb c0
      have hb0_mem : hub b0 ∈ S := (hhb c0).1
      have hconst : ∀ c : Fin q, hb c = b0 := by
        intro c
        by_contra hne
        have hcmem : hub (hb c) ∈ S := (hhb c).1
        cases hb0 : b0 <;> cases hbc : hb c
        · exact hne (hbc.trans hb0.symm)
        · rw [hb0] at hb0_mem; rw [hbc] at hcmem; exact hnot_both ⟨hb0_mem, hcmem⟩
        · rw [hb0] at hb0_mem; rw [hbc] at hcmem; exact hnot_both ⟨hcmem, hb0_mem⟩
        · exact hne (hbc.trans hb0.symm)
      have hstar_sub : star b0 ⊆ S := by
        intro x hx
        simp only [star, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
        rcases hx with rfl | ⟨c, rfl⟩
        · exact hb0_mem
        · rw [← hconst c]; exact (hhb c).2
      have hEq : star b0 = S :=
        Finset.eq_of_subset_of_card_le hstar_sub (by rw [hstar_card b0]; exact hScard)
      cases hb0 : b0
      · rw [hb0] at hEq; exact Or.inl hEq.symm
      · rw [hb0] at hEq; exact Or.inr hEq.symm
    · have hstar_ok : ∀ b : Bool, ¬ neutral (star b) ∧ ∀ c, desired c (star b) := by
        intro b
        constructor
        · rintro ⟨c, hf, ht⟩
          simp only [star, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hf ht
          rcases hf with hf | ⟨c1, hf⟩
          · exact (hub_ne_leaf b c false) hf.symm
          · rcases ht with ht | ⟨c2, ht⟩
            · exact (hub_ne_leaf b c true) ht.symm
            · have hb1 : b = false := (leaf_inj hf).2
              have hb2 : b = true := (leaf_inj ht).2
              have : false = true := hb1.symm.trans hb2
              simp at this
        · intro c
          left
          exact ⟨b, Finset.mem_insert_self _ _,
            Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ c))⟩
      rintro (rfl | rfl)
      · exact hstar_ok false
      · exact hstar_ok true

end PEqualNP.Outside.L_lib_884_aux

open PEqualNP.Outside.L_lib_884_aux in
theorem PEqualNP.Outside.L_lib_884 :
∀ (q k : Nat), 2 ≤ q →
  let V := Option (Fin q) × Bool
  ∀ name : V ↪ Fin k,
  let hub := fun b : Bool => name (none,b)
  let leaf := fun (c : Fin q) (b : Bool) => name (some c,b)
  let star := fun b : Bool => insert (hub b) (Finset.univ.image (fun c : Fin q => leaf c b))
  let neutral := fun S : Finset (Fin k) => ∃ c, leaf c false ∈ S ∧ leaf c true ∈ S
  let desired := fun (c : Fin q) (S : Finset (Fin k)) =>
    (∃ b, hub b ∈ S ∧ leaf c b ∈ S) ∨
    (∃ j, j ≠ c ∧ leaf j false ∈ S ∧ leaf j true ∈ S)
  (∀ P : Equiv.Perm (Fin k), Function.Involutive P →
    let hit := fun S : Finset (Fin k) => ∃ u ∈ S, P u ∈ S ∧ P u ≠ u
    let chosen := fun c : Fin q =>
      (∀ b, P (hub b) = leaf c b) ∧
      ∀ j, j ≠ c → P (leaf j false) = leaf j true
    ((∀ (c : Fin q) (b : Bool), hit {hub b, leaf c false, leaf c true}) ∧ hit (star false)) ↔
      ∃! c, chosen c) ∧
  ∀ S : Finset (Fin k), S.card ≤ q+1 →
    ((¬ neutral S ∧ ∀ c, desired c S) ↔ S = star false ∨ S = star true) :=
  main_proof
