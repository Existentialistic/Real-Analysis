import Mathlib.Tactic

open Nat

open BigOperators
open Finset

def sum_cubes (n : Nat) :  Nat :=
  ∑ i ∈ range (n + 1), i ^ 3

def triangle_sum (n : Nat) : Nat :=
  ∑ i ∈ range (n + 1), i

def triangle_sum_formula (n : Nat) : Nat :=
  (n * (n + 1)) / 2

lemma triangle_sum_proof : triangle_sum = triangle_sum_formula := by
  unfold triangle_sum triangle_sum_formula
  funext n
  induction n with
  |  zero =>
    rfl
  | succ n ih =>
    rw [range_eq_Ico]
    rw [sum_Ico_succ_top (zero_le)]
    rw [← range_eq_Ico]
    rw [ih]
    grind

theorem Nicomachus's_Theorem : sum_cubes = (triangle_sum) ^ 2 := by
  unfold sum_cubes triangle_sum
  funext n
  conv =>
    rhs;
    simp
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [range_eq_Ico]
    rw [sum_Ico_succ_top (zero_le)]
    rw [← range_eq_Ico]
    rw [ih]
    rw [sum_Ico_succ_top (zero_le)]
    rw [add_sq]
    rw [← range_eq_Ico]
    have h1 : (∑ i ∈ range (n + 1), i) = (∑ k ∈ range (n + 1), k) := by
      exact Finset.sum_congr rfl (fun _ _ => rfl)
    rw [h1]
    rw [add_assoc]
    rw [add_left_cancel_iff]
    have tsp := triangle_sum_proof
    unfold triangle_sum triangle_sum_formula at tsp
    have tsp := congrFun tsp n
    rw [tsp]
    rw [Nat.mul_div_cancel']
    · grind
    · exact two_dvd_mul_add_one n
