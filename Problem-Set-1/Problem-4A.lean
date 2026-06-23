import Mathlib.Tactic

open Nat

open BigOperators
open Finset

def binomial_left (a b : Int) (n : Nat) : Int :=
  (a + b)^n

def binomial_right (a b : Int) (n : Nat) : Int :=
  ∑ i ∈ range (n + 1),
  (a^i) * (b^(n - i)) * Nat.choose n i

theorem binomial_theorem : binomial_left = binomial_right := by
  unfold binomial_left binomial_right
  funext a b n
  rw [range_eq_Ico]
  --
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    rw [pow_add, pow_one, mul_add, ih]
    rw [mul_comm _ a, mul_comm _ b, mul_sum, mul_sum]
    conv =>
      lhs; rhs; rhs
      intro i
      rw [mul_comm (a ^ i) _,← mul_assoc, ← mul_assoc]
      lhs; lhs
      rw [mul_comm, ← pow_succ]
    conv =>
      lhs; rhs; rhs
      intro i
    conv =>
      lhs; lhs; rhs
      intro i
      rw [← mul_assoc, ← mul_assoc]
      lhs; lhs
      rw [mul_comm, ← pow_succ]
    conv =>
      lhs; rhs; rhs
      intro i
      rw [mul_comm _ (a ^ i)]
      lhs; rhs; rhs;
    --
    let f := fun x => a ^ (x) * b ^ (n - (x - 1)) * ↑(n.choose ((x - 1)))
    let f_shift := fun x => a ^ (x + 1) * b ^ (n - x) *
                      ↑(n.choose (x))
    have h1 {x : Nat} : f_shift (x) = f (x + 1) := by rfl
    --
    have h2 : ∑ i ∈ Ico 0 (n + 1), a ^ (i + 1) * b ^ (n - i) * ↑(n.choose i) =
        ∑ i ∈ Ico 0 (n + 1), f_shift i := by rfl
    --
    rw [h2]
    have h3 : ∑ i ∈ Ico 0 (n + 1), f_shift i = ∑ i ∈ Ico 0 (n + 1), f (i + 1) := by rfl
    --
    rw [h3]
    --
    rw [sum_Ico_add']
    rw [sum_Ico_succ_top (Nat.le_add_left 1 n)]
    --
    have h4 : ∑ i ∈ Ico 0 (n + 1), a ^ i * b ^ (n - i + 1) * ↑(n.choose i) =
        ∑ i ∈ Ico 0 (1), a ^ i * b ^ (n - i + 1) * ↑(n.choose i) +
        ∑ i ∈ Ico 1 (n + 1), a ^ i * b ^ (n - i + 1) * ↑(n.choose i) := by
      rw [sum_Ico_consecutive]
      · exact Nat.zero_le 1
      · exact Nat.le_add_left 1 n
    --
    rw [h4]
    rw [add_comm (∑ i ∈ Ico 0 1, a ^ i * b ^ (n - i + 1) * ↑(n.choose i)) _ ]
    rw [← add_assoc]
    rw [add_assoc _ (f (n + 1)) _]
    rw [add_comm (f (n + 1))]
    rw [← add_assoc]
    --
    have h5 : ∑ k ∈ Ico 1 (n + 1), f k = ∑ i ∈ Ico 1 (n + 1), a ^ (i) * b ^ (n - (i - 1))
      * ↑(n.choose ((i - 1))) := by
      rfl
    --
    rw [h5]
    rw [← sum_add_distrib]
    --
    have h6 : ∑ x ∈ Ico 1 (n + 1), (a ^ x * b ^ (n - (x - 1)) * ↑(n.choose (x - 1)) +
        a ^ x * b ^ (n - x + 1) * ↑(n.choose x)) =
        ∑ x ∈ Ico 1 (n + 1), (a ^ x * b ^ (n - x + 1) * ↑(n.choose (x - 1)) +
        a ^ x * b ^ (n - x + 1) * ↑(n.choose x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_Ico] at hx
      have hx1 : 1 ≤ x := hx.1
      have hx2 : x < n + 1 := hx.2
      congr 2
      congr 2
      omega
    rw [h6]
    --
    conv =>
      lhs; lhs; lhs; rhs;
      intro x
      rw [← mul_add (a ^ x * b ^ (n - x + 1)) _]
    --
    have h7 : ∀ x : Nat, ((↑(n.choose (x - 1)) : Int) + (↑(n.choose x)) : Int) =
        ((↑(((n + 1) - 1).choose (x - 1)) : Int) +
        (↑(((n + 1) - 1).choose x)) : Int) := by
        grind
    conv =>
      lhs; lhs; lhs; rhs
      intro x
      rhs;
      rw [h7]
    have h8 : ∑ x ∈ Ico 1 (n + 1), a ^ x * b ^ (n - x + 1) * (↑((n + 1 - 1).choose (x - 1)) +
        ↑((n + 1 - 1).choose x)) =
        ∑ x ∈ Ico 1 (n + 1), a ^ x * b ^ (n - x + 1) * (↑((n + 1).choose x)) := by
      apply sum_congr rfl
      intro x hx
      rw [Finset.mem_Ico] at hx
      congr 2
      norm_cast
      rw [← Nat.choose_eq_choose_pred_add]
      · omega
      · omega
    --
    rw [h8]
    have h9 : ∑ i ∈ Ico 0 (n + 1 + 1), a ^ i * b ^ (n + 1 - i) * ↑((n + 1).choose i) =
        ∑ i ∈ Ico 0 (1), a ^ i * b ^ (n + 1 - i) * ↑((n + 1).choose i) +
        ∑ i ∈ Ico 1 (n + 1 ), a ^ i * b ^ (n + 1 - i) * ↑((n + 1).choose i) +
        ∑ i ∈ Ico (n + 1) (n + 1 + 1), a ^ i * b ^ (n + 1 - i) * ↑((n + 1).choose i) := by
      repeat rw [sum_Ico_consecutive]
      · omega
      · omega
      · omega
      · omega
    --
    rw [h9]
    --
    have h10 : ∑ i ∈ Ico 1 (n + 1), a ^ i * b ^ (n + 1 - i) * ↑((n + 1).choose i) =
        ∑ x ∈ Ico 1 (n + 1), a ^ x * b ^ (n - x + 1) * ↑((n + 1).choose x) := by
      apply sum_congr rfl
      intro x hx
      rw [mem_Ico] at hx
      congr 2
      congr 2
      grind
    rw [h10]
    --
    have h11 : ∑ i ∈ Ico (n + 1) (n + 1 + 1), a ^ i * b ^ (n + 1 - i) * ↑((n + 1).choose i) =
        a ^ (n + 1) := by
      rw [sum_Ico_succ_top]
      · simp
      · omega
    --
    rw [h11]
    --
    have h12 : f (n + 1) = a ^ (n + 1) * b ^ (n - ((n + 1) - 1)) * ↑(n.choose (((n + 1) - 1))) := by
      rfl
    rw [h12]
    --
    have h13 : a ^ (n + 1) * b ^ (n - (n + 1 - 1)) * ↑(n.choose (n + 1 - 1)) = a ^ (n + 1) := by
      simp
    rw [h13]
    --
    simp only [Ico_succ_singleton, sum_singleton, pow_zero, tsub_zero, one_mul, choose_zero_right]
    simp only [cast_one, mul_one]
    rw [add_comm _ (b ^ (n + 1))]
    rw [add_assoc]
