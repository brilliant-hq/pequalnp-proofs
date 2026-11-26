import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18976

def candList : List ℕ :=
  [(67100672 : ℕ), (25018369 : ℕ), (7962627 : ℕ), (24444933 : ℕ), (7405575 : ℕ), (6815755 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (19988517 : ℕ), (19415081 : ℕ), (6619269 : ℕ), (2179233 : ℕ)]

def multList : List (Fin 13) :=
  [(1 : Fin 13), (3 : Fin 13), (9 : Fin 13)]

def wit0 (d1 d2 : Fin 13) : ℕ :=
  match d1.val with
  | 0 => match d2.val with
    | 0 => 25018369
    | 1 => 7962627
    | 2 => 24444933
    | 3 => 7962627
    | 4 => 7962627
    | 5 => 24444933
    | 6 => 24444933
    | 7 => 24444933
    | 8 => 24444933
    | 9 => 7962627
    | 10 => 7962627
    | 11 => 24444933
    | _ => 7962627
  | 1 => match d2.val with
    | 0 => 7962627
    | 1 => 7962627
    | 2 => 7405575
    | 3 => 6815755
    | 4 => 5799955
    | 5 => 23330829
    | 6 => 19415081
    | 7 => 22282261
    | 8 => 19988517
    | 9 => 6815755
    | 10 => 21757977
    | 11 => 23330829
    | _ => 7405575
  | 2 => match d2.val with
    | 0 => 24444933
    | 1 => 7405575
    | 2 => 24444933
    | 3 => 23330829
    | 4 => 22282261
    | 5 => 19988517
    | 6 => 19988517
    | 7 => 6619269
    | 8 => 2179233
    | 9 => 19415081
    | 10 => 19415081
    | 11 => 22282261
    | _ => 6815755
  | 3 => match d2.val with
    | 0 => 7962627
    | 1 => 6815755
    | 2 => 23330829
    | 3 => 7962627
    | 4 => 21757977
    | 5 => 19415081
    | 6 => 7405575
    | 7 => 23330829
    | 8 => 22282261
    | 9 => 6815755
    | 10 => 7405575
    | 11 => 19988517
    | _ => 5799955
  | 4 => match d2.val with
    | 0 => 7962627
    | 1 => 5799955
    | 2 => 22282261
    | 3 => 21757977
    | 4 => 7962627
    | 5 => 6815755
    | 6 => 19415081
    | 7 => 6815755
    | 8 => 7405575
    | 9 => 7405575
    | 10 => 23330829
    | 11 => 19988517
    | _ => 23330829
  | 5 => match d2.val with
    | 0 => 24444933
    | 1 => 23330829
    | 2 => 19988517
    | 3 => 19415081
    | 4 => 6815755
    | 5 => 24444933
    | 6 => 19988517
    | 7 => 2179233
    | 8 => 22282261
    | 9 => 7405575
    | 10 => 22282261
    | 11 => 6619269
    | _ => 19415081
  | 6 => match d2.val with
    | 0 => 24444933
    | 1 => 19415081
    | 2 => 19988517
    | 3 => 7405575
    | 4 => 19415081
    | 5 => 19988517
    | 6 => 24444933
    | 7 => 22282261
    | 8 => 6619269
    | 9 => 23330829
    | 10 => 6815755
    | 11 => 2179233
    | _ => 22282261
  | 7 => match d2.val with
    | 0 => 24444933
    | 1 => 22282261
    | 2 => 6619269
    | 3 => 23330829
    | 4 => 6815755
    | 5 => 2179233
    | 6 => 22282261
    | 7 => 24444933
    | 8 => 19415081
    | 9 => 19988517
    | 10 => 7405575
    | 11 => 19415081
    | _ => 19988517
  | 8 => match d2.val with
    | 0 => 24444933
    | 1 => 19988517
    | 2 => 2179233
    | 3 => 22282261
    | 4 => 7405575
    | 5 => 22282261
    | 6 => 6619269
    | 7 => 19415081
    | 8 => 24444933
    | 9 => 23330829
    | 10 => 19988517
    | 11 => 19415081
    | _ => 6815755
  | 9 => match d2.val with
    | 0 => 7962627
    | 1 => 6815755
    | 2 => 19415081
    | 3 => 6815755
    | 4 => 7405575
    | 5 => 7405575
    | 6 => 23330829
    | 7 => 19988517
    | 8 => 23330829
    | 9 => 7962627
    | 10 => 5799955
    | 11 => 22282261
    | _ => 21757977
  | 10 => match d2.val with
    | 0 => 7962627
    | 1 => 21757977
    | 2 => 19415081
    | 3 => 7405575
    | 4 => 23330829
    | 5 => 22282261
    | 6 => 6815755
    | 7 => 7405575
    | 8 => 19988517
    | 9 => 5799955
    | 10 => 7962627
    | 11 => 6815755
    | _ => 23330829
  | 11 => match d2.val with
    | 0 => 24444933
    | 1 => 23330829
    | 2 => 22282261
    | 3 => 19988517
    | 4 => 19988517
    | 5 => 6619269
    | 6 => 2179233
    | 7 => 19415081
    | 8 => 19415081
    | 9 => 22282261
    | 10 => 6815755
    | 11 => 24444933
    | _ => 7405575
  | _ => match d2.val with
    | 0 => 7962627
    | 1 => 7405575
    | 2 => 6815755
    | 3 => 5799955
    | 4 => 23330829
    | 5 => 19415081
    | 6 => 22282261
    | 7 => 19988517
    | 8 => 6815755
    | 9 => 21757977
    | 10 => 23330829
    | 11 => 7405575
    | _ => 7962627

def wit1 (d1 d2 : Fin 13) : Fin 13 :=
  match d1.val with
  | 0 => match d2.val with
    | 0 => (1 : Fin 13)
    | 1 => (1 : Fin 13)
    | 2 => (1 : Fin 13)
    | 3 => (9 : Fin 13)
    | 4 => (3 : Fin 13)
    | 5 => (3 : Fin 13)
    | 6 => (9 : Fin 13)
    | 7 => (9 : Fin 13)
    | 8 => (3 : Fin 13)
    | 9 => (3 : Fin 13)
    | 10 => (9 : Fin 13)
    | 11 => (1 : Fin 13)
    | _ => (1 : Fin 13)
  | 1 => match d2.val with
    | 0 => (1 : Fin 13)
    | 1 => (1 : Fin 13)
    | 2 => (1 : Fin 13)
    | 3 => (1 : Fin 13)
    | 4 => (1 : Fin 13)
    | 5 => (3 : Fin 13)
    | 6 => (3 : Fin 13)
    | 7 => (9 : Fin 13)
    | 8 => (3 : Fin 13)
    | 9 => (3 : Fin 13)
    | 10 => (1 : Fin 13)
    | 11 => (1 : Fin 13)
    | _ => (1 : Fin 13)
  | 2 => match d2.val with
    | 0 => (1 : Fin 13)
    | 1 => (1 : Fin 13)
    | 2 => (1 : Fin 13)
    | 3 => (1 : Fin 13)
    | 4 => (1 : Fin 13)
    | 5 => (1 : Fin 13)
    | 6 => (9 : Fin 13)
    | 7 => (1 : Fin 13)
    | 8 => (1 : Fin 13)
    | 9 => (9 : Fin 13)
    | 10 => (1 : Fin 13)
    | 11 => (1 : Fin 13)
    | _ => (1 : Fin 13)
  | 3 => match d2.val with
    | 0 => (9 : Fin 13)
    | 1 => (1 : Fin 13)
    | 2 => (1 : Fin 13)
    | 3 => (9 : Fin 13)
    | 4 => (1 : Fin 13)
    | 5 => (1 : Fin 13)
    | 6 => (9 : Fin 13)
    | 7 => (9 : Fin 13)
    | 8 => (3 : Fin 13)
    | 9 => (9 : Fin 13)
    | 10 => (9 : Fin 13)
    | 11 => (1 : Fin 13)
    | _ => (1 : Fin 13)
  | 4 => match d2.val with
    | 0 => (3 : Fin 13)
    | 1 => (1 : Fin 13)
    | 2 => (1 : Fin 13)
    | 3 => (1 : Fin 13)
    | 4 => (3 : Fin 13)
    | 5 => (3 : Fin 13)
    | 6 => (9 : Fin 13)
    | 7 => (9 : Fin 13)
    | 8 => (3 : Fin 13)
    | 9 => (3 : Fin 13)
    | 10 => (9 : Fin 13)
    | 11 => (9 : Fin 13)
    | _ => (3 : Fin 13)
  | 5 => match d2.val with
    | 0 => (3 : Fin 13)
    | 1 => (3 : Fin 13)
    | 2 => (1 : Fin 13)
    | 3 => (1 : Fin 13)
    | 4 => (3 : Fin 13)
    | 5 => (3 : Fin 13)
    | 6 => (3 : Fin 13)
    | 7 => (1 : Fin 13)
    | 8 => (3 : Fin 13)
    | 9 => (3 : Fin 13)
    | 10 => (3 : Fin 13)
    | 11 => (1 : Fin 13)
    | _ => (3 : Fin 13)
  | 6 => match d2.val with
    | 0 => (9 : Fin 13)
    | 1 => (3 : Fin 13)
    | 2 => (9 : Fin 13)
    | 3 => (9 : Fin 13)
    | 4 => (9 : Fin 13)
    | 5 => (3 : Fin 13)
    | 6 => (9 : Fin 13)
    | 7 => (9 : Fin 13)
    | 8 => (1 : Fin 13)
    | 9 => (9 : Fin 13)
    | 10 => (9 : Fin 13)
    | 11 => (1 : Fin 13)
    | _ => (9 : Fin 13)
  | 7 => match d2.val with
    | 0 => (9 : Fin 13)
    | 1 => (9 : Fin 13)
    | 2 => (1 : Fin 13)
    | 3 => (9 : Fin 13)
    | 4 => (9 : Fin 13)
    | 5 => (1 : Fin 13)
    | 6 => (9 : Fin 13)
    | 7 => (9 : Fin 13)
    | 8 => (3 : Fin 13)
    | 9 => (9 : Fin 13)
    | 10 => (9 : Fin 13)
    | 11 => (9 : Fin 13)
    | _ => (3 : Fin 13)
  | 8 => match d2.val with
    | 0 => (3 : Fin 13)
    | 1 => (3 : Fin 13)
    | 2 => (1 : Fin 13)
    | 3 => (3 : Fin 13)
    | 4 => (3 : Fin 13)
    | 5 => (3 : Fin 13)
    | 6 => (1 : Fin 13)
    | 7 => (3 : Fin 13)
    | 8 => (3 : Fin 13)
    | 9 => (3 : Fin 13)
    | 10 => (1 : Fin 13)
    | 11 => (1 : Fin 13)
    | _ => (3 : Fin 13)
  | 9 => match d2.val with
    | 0 => (3 : Fin 13)
    | 1 => (3 : Fin 13)
    | 2 => (9 : Fin 13)
    | 3 => (9 : Fin 13)
    | 4 => (3 : Fin 13)
    | 5 => (3 : Fin 13)
    | 6 => (9 : Fin 13)
    | 7 => (9 : Fin 13)
    | 8 => (3 : Fin 13)
    | 9 => (3 : Fin 13)
    | 10 => (1 : Fin 13)
    | 11 => (1 : Fin 13)
    | _ => (1 : Fin 13)
  | 10 => match d2.val with
    | 0 => (9 : Fin 13)
    | 1 => (1 : Fin 13)
    | 2 => (1 : Fin 13)
    | 3 => (9 : Fin 13)
    | 4 => (9 : Fin 13)
    | 5 => (3 : Fin 13)
    | 6 => (9 : Fin 13)
    | 7 => (9 : Fin 13)
    | 8 => (1 : Fin 13)
    | 9 => (1 : Fin 13)
    | 10 => (9 : Fin 13)
    | 11 => (1 : Fin 13)
    | _ => (1 : Fin 13)
  | 11 => match d2.val with
    | 0 => (1 : Fin 13)
    | 1 => (1 : Fin 13)
    | 2 => (1 : Fin 13)
    | 3 => (1 : Fin 13)
    | 4 => (9 : Fin 13)
    | 5 => (1 : Fin 13)
    | 6 => (1 : Fin 13)
    | 7 => (9 : Fin 13)
    | 8 => (1 : Fin 13)
    | 9 => (1 : Fin 13)
    | 10 => (1 : Fin 13)
    | 11 => (1 : Fin 13)
    | _ => (1 : Fin 13)
  | _ => match d2.val with
    | 0 => (1 : Fin 13)
    | 1 => (1 : Fin 13)
    | 2 => (1 : Fin 13)
    | 3 => (1 : Fin 13)
    | 4 => (3 : Fin 13)
    | 5 => (3 : Fin 13)
    | 6 => (9 : Fin 13)
    | 7 => (3 : Fin 13)
    | 8 => (3 : Fin 13)
    | 9 => (1 : Fin 13)
    | 10 => (1 : Fin 13)
    | 11 => (1 : Fin 13)
    | _ => (1 : Fin 13)

def wit2 (d1 d2 : Fin 13) : Fin 13 :=
  match d1.val with
  | 0 => match d2.val with
    | 0 => (0 : Fin 13)
    | 1 => (0 : Fin 13)
    | 2 => (0 : Fin 13)
    | 3 => (0 : Fin 13)
    | 4 => (1 : Fin 13)
    | 5 => (0 : Fin 13)
    | 6 => (0 : Fin 13)
    | 7 => (2 : Fin 13)
    | 8 => (2 : Fin 13)
    | 9 => (0 : Fin 13)
    | 10 => (1 : Fin 13)
    | 11 => (2 : Fin 13)
    | _ => (1 : Fin 13)
  | 1 => match d2.val with
    | 0 => (0 : Fin 13)
    | 1 => (0 : Fin 13)
    | 2 => (0 : Fin 13)
    | 3 => (0 : Fin 13)
    | 4 => (0 : Fin 13)
    | 5 => (0 : Fin 13)
    | 6 => (0 : Fin 13)
    | 7 => (4 : Fin 13)
    | 8 => (2 : Fin 13)
    | 9 => (0 : Fin 13)
    | 10 => (3 : Fin 13)
    | 11 => (2 : Fin 13)
    | _ => (1 : Fin 13)
  | 2 => match d2.val with
    | 0 => (0 : Fin 13)
    | 1 => (0 : Fin 13)
    | 2 => (0 : Fin 13)
    | 3 => (0 : Fin 13)
    | 4 => (0 : Fin 13)
    | 5 => (0 : Fin 13)
    | 6 => (0 : Fin 13)
    | 7 => (0 : Fin 13)
    | 8 => (5 : Fin 13)
    | 9 => (0 : Fin 13)
    | 10 => (3 : Fin 13)
    | 11 => (2 : Fin 13)
    | _ => (1 : Fin 13)
  | 3 => match d2.val with
    | 0 => (0 : Fin 13)
    | 1 => (0 : Fin 13)
    | 2 => (0 : Fin 13)
    | 3 => (0 : Fin 13)
    | 4 => (0 : Fin 13)
    | 5 => (0 : Fin 13)
    | 6 => (0 : Fin 13)
    | 7 => (2 : Fin 13)
    | 8 => (4 : Fin 13)
    | 9 => (0 : Fin 13)
    | 10 => (1 : Fin 13)
    | 11 => (2 : Fin 13)
    | _ => (1 : Fin 13)
  | 4 => match d2.val with
    | 0 => (1 : Fin 13)
    | 1 => (0 : Fin 13)
    | 2 => (0 : Fin 13)
    | 3 => (0 : Fin 13)
    | 4 => (1 : Fin 13)
    | 5 => (1 : Fin 13)
    | 6 => (3 : Fin 13)
    | 7 => (3 : Fin 13)
    | 8 => (2 : Fin 13)
    | 9 => (1 : Fin 13)
    | 10 => (3 : Fin 13)
    | 11 => (5 : Fin 13)
    | _ => (3 : Fin 13)
  | 5 => match d2.val with
    | 0 => (0 : Fin 13)
    | 1 => (0 : Fin 13)
    | 2 => (0 : Fin 13)
    | 3 => (0 : Fin 13)
    | 4 => (1 : Fin 13)
    | 5 => (0 : Fin 13)
    | 6 => (0 : Fin 13)
    | 7 => (0 : Fin 13)
    | 8 => (2 : Fin 13)
    | 9 => (0 : Fin 13)
    | 10 => (0 : Fin 13)
    | 11 => (2 : Fin 13)
    | _ => (3 : Fin 13)
  | 6 => match d2.val with
    | 0 => (0 : Fin 13)
    | 1 => (0 : Fin 13)
    | 2 => (0 : Fin 13)
    | 3 => (0 : Fin 13)
    | 4 => (3 : Fin 13)
    | 5 => (0 : Fin 13)
    | 6 => (0 : Fin 13)
    | 7 => (2 : Fin 13)
    | 8 => (7 : Fin 13)
    | 9 => (0 : Fin 13)
    | 10 => (1 : Fin 13)
    | 11 => (7 : Fin 13)
    | _ => (0 : Fin 13)
  | 7 => match d2.val with
    | 0 => (2 : Fin 13)
    | 1 => (4 : Fin 13)
    | 2 => (0 : Fin 13)
    | 3 => (2 : Fin 13)
    | 4 => (3 : Fin 13)
    | 5 => (0 : Fin 13)
    | 6 => (2 : Fin 13)
    | 7 => (2 : Fin 13)
    | 8 => (5 : Fin 13)
    | 9 => (2 : Fin 13)
    | 10 => (2 : Fin 13)
    | 11 => (5 : Fin 13)
    | _ => (5 : Fin 13)
  | 8 => match d2.val with
    | 0 => (2 : Fin 13)
    | 1 => (2 : Fin 13)
    | 2 => (5 : Fin 13)
    | 3 => (4 : Fin 13)
    | 4 => (2 : Fin 13)
    | 5 => (2 : Fin 13)
    | 6 => (7 : Fin 13)
    | 7 => (5 : Fin 13)
    | 8 => (2 : Fin 13)
    | 9 => (2 : Fin 13)
    | 10 => (5 : Fin 13)
    | 11 => (5 : Fin 13)
    | _ => (3 : Fin 13)
  | 9 => match d2.val with
    | 0 => (0 : Fin 13)
    | 1 => (0 : Fin 13)
    | 2 => (0 : Fin 13)
    | 3 => (0 : Fin 13)
    | 4 => (1 : Fin 13)
    | 5 => (0 : Fin 13)
    | 6 => (0 : Fin 13)
    | 7 => (2 : Fin 13)
    | 8 => (2 : Fin 13)
    | 9 => (0 : Fin 13)
    | 10 => (4 : Fin 13)
    | 11 => (4 : Fin 13)
    | _ => (4 : Fin 13)
  | 10 => match d2.val with
    | 0 => (1 : Fin 13)
    | 1 => (3 : Fin 13)
    | 2 => (3 : Fin 13)
    | 3 => (1 : Fin 13)
    | 4 => (3 : Fin 13)
    | 5 => (0 : Fin 13)
    | 6 => (1 : Fin 13)
    | 7 => (2 : Fin 13)
    | 8 => (5 : Fin 13)
    | 9 => (4 : Fin 13)
    | 10 => (1 : Fin 13)
    | 11 => (3 : Fin 13)
    | _ => (3 : Fin 13)
  | 11 => match d2.val with
    | 0 => (2 : Fin 13)
    | 1 => (2 : Fin 13)
    | 2 => (2 : Fin 13)
    | 3 => (2 : Fin 13)
    | 4 => (5 : Fin 13)
    | 5 => (2 : Fin 13)
    | 6 => (7 : Fin 13)
    | 7 => (5 : Fin 13)
    | 8 => (5 : Fin 13)
    | 9 => (4 : Fin 13)
    | 10 => (3 : Fin 13)
    | 11 => (2 : Fin 13)
    | _ => (2 : Fin 13)
  | _ => match d2.val with
    | 0 => (1 : Fin 13)
    | 1 => (1 : Fin 13)
    | 2 => (1 : Fin 13)
    | 3 => (1 : Fin 13)
    | 4 => (3 : Fin 13)
    | 5 => (3 : Fin 13)
    | 6 => (0 : Fin 13)
    | 7 => (5 : Fin 13)
    | 8 => (3 : Fin 13)
    | 9 => (4 : Fin 13)
    | 10 => (3 : Fin 13)
    | 11 => (2 : Fin 13)
    | _ => (1 : Fin 13)

private lemma cover_empty :
    ∃ x3 ∈ candList, ∃ x4 ∈ multList, ∃ x5 : Fin 13,
    ∀ x6 : Fin 13, false = x3.testBit ↑(x4 * x6 + x5) := by
  refine ⟨67100672, by simp [candList], 1, by simp [multList], 0, ?_⟩
  decide

private lemma wit_mem3 : ∀ d1 d2 : Fin 13, wit0 d1 d2 ∈ candList := by
  decide

private lemma wit_mem4 : ∀ d1 d2 : Fin 13, wit1 d1 d2 ∈ multList := by
  decide

private lemma wit_bits : ∀ d1 d2 y : Fin 13,
    Decidable.decide (y = 0 ∨ y = d1 ∨ y = d2) =
      (wit0 d1 d2).testBit ↑((wit1 d1 d2) * y + (wit2 d1 d2)) := by
  decide

private lemma fin13_mul_sub_add (a x4 x6 : Fin 13) :
    x4 * (x6 - a) + x4 * a = x4 * x6 := by
  revert a x4 x6; decide

private lemma fin13_add_sub_cancel (u v : Fin 13) :
    u + (v - u) = v := by
  revert u v; decide

private lemma fin13_shift (a x4 x5 x6 : Fin 13) :
    x4 * (x6 - a) + x5 = x4 * x6 + (x5 - x4 * a) := by
  calc x4 * (x6 - a) + x5
      = x4 * (x6 - a) + (x4 * a + (x5 - x4 * a)) := by
          rw [fin13_add_sub_cancel]
    _ = (x4 * (x6 - a) + x4 * a) + (x5 - x4 * a) := by
          rw [add_assoc]
    _ = x4 * x6 + (x5 - x4 * a) := by
          rw [fin13_mul_sub_add]

private lemma exists_triple {α : Type*} [DecidableEq α] (s : Finset α) (hne : s.Nonempty) (hc : s.card ≤ 3) :
    ∃ a b c : α, ∀ z : α, z ∈ s ↔ z = a ∨ z = b ∨ z = c := by
  obtain ⟨a, ha⟩ := hne
  rcases (s.erase a).eq_empty_or_nonempty with h1 | ⟨b, hb⟩
  · refine ⟨a, a, a, fun z => ?_⟩
    constructor
    · intro hz
      by_cases hza : z = a
      · exact Or.inl hza
      · exfalso
        have : z ∈ s.erase a := Finset.mem_erase.mpr ⟨hza, hz⟩
        rw [h1] at this
        exact Finset.notMem_empty z this
    · rintro (rfl | rfl | rfl) <;> exact ha
  · have hb_s : b ∈ s := Finset.mem_of_mem_erase hb
    rcases ((s.erase a).erase b).eq_empty_or_nonempty with h2 | ⟨c, hc_mem⟩
    · refine ⟨a, b, b, fun z => ?_⟩
      constructor
      · intro hz
        by_cases hza : z = a
        · exact Or.inl hza
        · by_cases hzb : z = b
          · exact Or.inr (Or.inl hzb)
          · exfalso
            have : z ∈ (s.erase a).erase b := Finset.mem_erase.mpr ⟨hzb, Finset.mem_erase.mpr ⟨hza, hz⟩⟩
            rw [h2] at this
            exact Finset.notMem_empty z this
      · rintro (rfl | rfl | rfl)
        · exact ha
        · exact hb_s
        · exact hb_s
    · have hc_s : c ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc_mem)
      have hcard1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
      have hcard2 : ((s.erase a).erase b).card = (s.erase a).card - 1 := Finset.card_erase_of_mem hb
      have hcard3 : (((s.erase a).erase b).erase c).card = ((s.erase a).erase b).card - 1 :=
        Finset.card_erase_of_mem hc_mem
      have h3_empty : ((s.erase a).erase b).erase c = ∅ := by
        apply Finset.card_eq_zero.mp
        omega
      refine ⟨a, b, c, fun z => ?_⟩
      constructor
      · intro hz
        by_cases hza : z = a
        · exact Or.inl hza
        · by_cases hzb : z = b
          · exact Or.inr (Or.inl hzb)
          · by_cases hzc : z = c
            · exact Or.inr (Or.inr hzc)
            · exfalso
              have : z ∈ ((s.erase a).erase b).erase c :=
                Finset.mem_erase.mpr ⟨hzc, Finset.mem_erase.mpr ⟨hzb, Finset.mem_erase.mpr ⟨hza, hz⟩⟩⟩
              rw [h3_empty] at this
              exact Finset.notMem_empty z this
      · rintro (rfl | rfl | rfl)
        · exact ha
        · exact hb_s
        · exact hc_s

end PEqualNP.Outside.L_meta_18976

theorem PEqualNP.Outside.L_meta_18976 : (∀ (x1 : Finset (Fin (13 : ℕ))), x1.card ≤ (3 : ℕ) → ∃ x3 ∈ [(67100672 : ℕ), (25018369 : ℕ), (7962627 : ℕ), (24444933 : ℕ), (7405575 : ℕ), (6815755 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (19988517 : ℕ), (19415081 : ℕ), (6619269 : ℕ), (2179233 : ℕ)], ∃ x4 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), Decidable.decide (x6 ∈ x1) = x3.testBit ↑(x4 * x6 + x5)) := by
  intro x1 hcard
  rcases x1.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨x3, hx3, x4, hx4, x5, h⟩ := L_meta_18976.cover_empty
    exact ⟨x3, hx3, x4, hx4, x5, fun x6 => by simpa using h x6⟩
  · obtain ⟨a, b, c, habc⟩ := L_meta_18976.exists_triple x1 hne hcard
    let d1 := b - a
    let d2 := c - a
    let x3 := L_meta_18976.wit0 d1 d2
    let x4 := L_meta_18976.wit1 d1 d2
    let x5 := L_meta_18976.wit2 d1 d2
    refine ⟨x3, L_meta_18976.wit_mem3 d1 d2, x4, L_meta_18976.wit_mem4 d1 d2, x5 - x4 * a, fun x6 => ?_⟩
    have hmem : (x6 ∈ x1) ↔ (x6 - a = 0 ∨ x6 - a = d1 ∨ x6 - a = d2) := by
      rw [habc x6]
      simp [d1, d2, sub_eq_zero, sub_left_inj]
    have harg := L_meta_18976.fin13_shift a x4 x5 x6
    have hdec : Decidable.decide (x6 ∈ x1) = Decidable.decide (x6 - a = 0 ∨ x6 - a = d1 ∨ x6 - a = d2) :=
      decide_eq_decide.mpr hmem
    rw [hdec, ← harg]
    exact L_meta_18976.wit_bits d1 d2 (x6 - a)
