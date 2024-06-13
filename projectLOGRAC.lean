import Mathlib
open BigOperators
open Finset
open Finset.antidiagonal

/-- 1st SMALL TASK:
Formalize the recursive definition of the catalan numbers. --/

def catalan_number : ℕ → ℕ
| 0 => 1
| (n+1) => ∑ i : Fin n.succ, catalan_number i * catalan_number (n-i)

/-- 2nd SMALL TASK:
Formalize the concept of plane trees. --/

inductive plane_tree : Type
| node : List plane_tree → plane_tree

/-- 3rd SMALL TASK
Formalize the concept of full binary trees. --/

inductive full_binary_tree : Type
| leaf : full_binary_tree
| node₂ : (T1 T2 : full_binary_tree) → full_binary_tree

/- The height of a full binary tree -/

def full_binary_tree.height : full_binary_tree → ℕ
| .leaf => 1
| .node₂ T1 T2 => max T1.height T2.height + 1

/- The number of nodes (including leaves) of full binary trees -/

def full_binary_tree.number_of_nodes : full_binary_tree → ℕ
| .leaf => 1
| .node₂ T1 T2 => T1.number_of_nodes + T2.number_of_nodes + 1

/-- 4th SMALL TASK:
Construct the type of full binary trees with n nodes, not counting the leaves. --/

inductive full_binary_tree_with_nodes : ℕ → Type
| leaf : full_binary_tree_with_nodes 0
| node₂ :
  {m n : ℕ} →
  full_binary_tree_with_nodes m →
  full_binary_tree_with_nodes n →
  full_binary_tree_with_nodes (m + n + 1)

/-- 5th SMALL TASK:
Define the type of ballot sequences of length n.

Recognizing ballot sequences: --/
def is_ballot_sequence : List ℤ → ℤ → Bool
| [], sum => sum ≥ 0
| (x :: xs), sum => (sum + x : ℤ) ≥ 0 ∧ is_ballot_sequence xs (sum + x)

/- Constructing general sequences of 1s and -1s of lenght n: -/
def generate_sequences : ℕ → List (List ℤ)
| 0 => [[]]
| (n + 1) => generate_sequences n >>= λ seq => [1 :: seq, -1 :: seq]

/- Defining ballot sequences of length n: -/
def generate_ballot_sequences (n : ℕ) : List (List ℤ) :=
  (generate_sequences n).filter (λ seq => is_ballot_sequence seq 0)


/-- 4th LARGE TASK:
Construct a bijection between list plane trees and plane trees. --/

def plane_tree_to_list_plane_tree: plane_tree → List plane_tree
| plane_tree.node T => T

def list_plane_tree_to_plane_tree: List plane_tree → plane_tree
| T => plane_tree.node T

/-- List plane tree -> plane tree: --/
theorem list_plane_tree_to_plane_tree_inverse :
  ∀ (T : List plane_tree),
  T = plane_tree_to_list_plane_tree (list_plane_tree_to_plane_tree T) := by
intro T
induction T with
| nil => rfl
| cons h t => simp [list_plane_tree_to_plane_tree, plane_tree_to_list_plane_tree]

/-- plane tree -> List plane tree: --/
theorem plane_tree_to_list_plane_tree_inverse :
  ∀ (T : plane_tree),
  T = list_plane_tree_to_plane_tree (plane_tree_to_list_plane_tree T) := by
intro T
cases T with
| node T =>
  cases T with
  | nil => simp [plane_tree_to_list_plane_tree, list_plane_tree_to_plane_tree]
  | cons h t => simp [plane_tree_to_list_plane_tree, list_plane_tree_to_plane_tree]

/-- 5th LARGE TASK:
Construct the rotating isomorphism
(the isomorphism between plane trees and full binary trees) --/

def full_binary_tree_to_plane_tree : full_binary_tree → plane_tree
| full_binary_tree.leaf => plane_tree.node List.nil
| full_binary_tree.node₂ T1 T2 =>
  plane_tree.node (List.cons (full_binary_tree_to_plane_tree T1) (plane_tree_to_list_plane_tree (full_binary_tree_to_plane_tree T2)))

def plane_tree_to_full_binary_tree : plane_tree → full_binary_tree
  | plane_tree.node List.nil => full_binary_tree.leaf
  | plane_tree.node (h :: t) => full_binary_tree.node₂ (plane_tree_to_full_binary_tree h) (plane_tree_to_full_binary_tree (plane_tree.node t))

/-- full binary tree -> plane tree: --/
theorem full_binary_tree_to_plane_tree_inverse :
  ∀ (T : full_binary_tree),
  T = plane_tree_to_full_binary_tree (full_binary_tree_to_plane_tree T) := by
intro T
induction T with
| leaf => rfl
| node₂ T1 T2 HT1 HT2 =>
  simp [full_binary_tree_to_plane_tree, plane_tree_to_full_binary_tree, plane_tree_to_list_plane_tree]
  rw[←HT1]
  apply And.intro
  tauto
  split
  case node₂ type TT =>
    rw[←TT, ←HT2]

/-- plane tree -> full binary tree: --/
theorem plane_tree_to_full_binary_tree_inverse :
  ∀ (T : plane_tree),
  T = full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree T) := by
  intro T
  cases T with
  | node l =>
    cases l with
    | nil => rfl
    | cons T l =>
      rw [plane_tree_to_full_binary_tree]
      simp [full_binary_tree_to_plane_tree]
      apply And.intro
      rw [←plane_tree_to_full_binary_tree_inverse]
      rw [←plane_tree_to_full_binary_tree_inverse, plane_tree_to_list_plane_tree]

/-- 6th LARGE TASK:

theorem binom_divisible_by_n_plus_1 (n : ℕ) : ((Nat.choose (2 * n) n)) % (n + 1) = 0 := by
  have h : (Nat.choose (2 * n) n) =  1/n * (Nat.choose (2*n) (n + 1)) * (n+1) := by
    have h1 : (2 * n - n) = n := by
      rw [two_mul, Nat.add_sub_assoc, Nat.sub_self, add_zero]
      rfl
    have h2 : (2 * n - (n + 1)) =  (n - 1) := by
      rw [Nat.two_mul, Nat.sub_add_eq, Nat.add_sub_assoc, Nat.sub_self, add_zero]
      rfl
    rw [Nat.choose_eq_factorial_div_factorial, Nat.choose_eq_factorial_div_factorial, h1, h2]
    sorry
  rw [h, Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod]
