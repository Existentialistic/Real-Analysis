import Mathlib.Tactic

def reflexive (α : Type) (r : α → α → Prop) : Prop :=
  (∀ x, r x x)

def symmetric (α : Type) (r : α → α → Prop) : Prop :=
  (∀ x y, r x y ↔ r y x)

def transitive (α : Type) (r : α → α → Prop) : Prop :=
  (∀ x y z, r x y → r y z → r x z)

def equivalence (α : Type) (r : α → α → Prop) : Prop :=
  reflexive α r ∧ symmetric α r ∧ transitive α r

def eq_parity (a : ℤ) (b : ℤ) : Prop :=
  (Even a ∧ Even b) ∨ (Odd a ∧ Odd b)

theorem eq_parity_equivalence : equivalence (ℤ : Type) eq_parity := by
  unfold equivalence eq_parity
  constructor
  · unfold reflexive
    simp only [and_self]
    exact Int.even_or_odd
  · constructor
    · unfold symmetric
      intro x y
      simp only
      grind
    · unfold transitive
      intro x y z
      simp only
      rintro (hxy | hxy) (hyz | hyz)
      · exact Or.inl ⟨hxy.left, hyz.right⟩
      · exact absurd hyz.left (Int.not_odd_iff_even.mpr hxy.right)
      · exact absurd hxy.right (Int.not_odd_iff_even.mpr hyz.left)
      · exact Or.inr ⟨hxy.left, hyz.right⟩

def eq_mod_k (k : ℤ) (x : ℤ) (y : ℤ) : Prop :=
  ∃ n, n * k = x - y

theorem eq_mod_k_equivalence :
    ∀ k, equivalence (ℤ : Type) (eq_mod_k k) := by
  intro k
  unfold equivalence eq_mod_k
  constructor
  · unfold reflexive
    intro x
    use 0
    grind only
  · constructor
    · unfold symmetric
      intro x y
      simp only
      constructor <;> (intro ⟨n, hn⟩; use -n; grind only)
    · unfold transitive
      intro x y z ⟨n, hxy⟩ ⟨m, hyz⟩
      use n + m
      grind only

def diff_rat_is_int (a b : ℚ) : Prop :=
  Rat.isInt (a - b)

theorem diff_rat_is_int_equivalence :
    equivalence (ℚ : Type) diff_rat_is_int := by
  unfold equivalence diff_rat_is_int
  constructor
  · unfold reflexive
    intro x
    rw [sub_self]
    rfl
  · constructor
    · unfold symmetric
      intro x y
      simp only
      constructor
      · repeat rw [Rat.isInt, beq_iff_eq]
        intro h
        rw [Eq.symm (Rat.neg_sub x y)]
        rw [Rat.neg_den]
        exact h
      · repeat rw [Rat.isInt, beq_iff_eq]
        intro h
        rw [Eq.symm (Rat.neg_sub y x)]
        rw [Rat.neg_den]
        exact h
    · unfold transitive
      intro x y z hxy hyz
      repeat rw [Rat.isInt, beq_iff_eq]
      repeat rw [Rat.isInt, beq_iff_eq] at hxy
      repeat rw [Rat.isInt, beq_iff_eq] at hyz
      have h1 : x - y = ((x - y).num : ℚ) := by
        nth_rw 1 [← Rat.num_div_den (x - y)]
        rw [hxy]
        simp only [Nat.cast_one, div_one]
      have h2 : y - z = ((y - z).num : ℚ) := by
        nth_rw 1 [← Rat.num_div_den (y - z)]
        rw [hyz]
        simp only [Nat.cast_one, div_one]
      have h3 : x - z = (x - y) + (y - z) := by norm_num
      rw [h3, h1, h2]
      simp only [Rat.add_intCast_den, Rat.den_intCast]

def diff_one (a b : ℚ) : Prop :=
  |a - b| < 1

theorem diff_one_not_equivalence : ¬equivalence ℚ diff_one := by
  unfold equivalence diff_one
  repeat rw [not_and]
  intro _ _
  unfold transitive
  simp only
  push Not
  use 0, 1/2, 1
  grind

def int_interval (a b : ℚ) : Prop :=
  ∃ n : ℤ, (n ≤ a) ∧ (a < n + 1) ∧ (n ≤ b) ∧ (b < n + 1)

theorem int_interval_equivalence : equivalence (ℚ : Type) int_interval := by
  unfold equivalence int_interval
  constructor
  · unfold reflexive
    intro x
    use ⌊x⌋
    norm_num
    exact_mod_cast Int.floor_le x
  · constructor
    · unfold symmetric
      intro x y
      simp only
      constructor
      · rintro ⟨n, hx1, hx2, hy1, hy2⟩; exact ⟨n, hy1, hy2, hx1, hx2⟩
      · rintro ⟨n, hy1, hy2, hx1, hx2⟩; exact ⟨n, hx1, hx2, hy1, hy2⟩
    · unfold transitive
      intro x y z hx hy
      obtain ⟨n, ⟨hnx1, hnx2, hny1, hny2⟩⟩ := hx
      obtain ⟨k, ⟨hky1, hky2, hkz1, hkz2⟩⟩ := hy
      have n_eq_k : n = k := by
        have n_leq_k : n ≤ k := by
          have n_lt_k_plus_one : n < k + 1 := by
            have n_rat : (n : ℚ) < k + 1 := by linarith [hny1, hky2]
            exact_mod_cast n_rat
          exact Int.le_of_lt_add_one n_lt_k_plus_one
        --
        have k_leq_n : k ≤ n := by
          have k_lt_n_plus_one : k < n + 1 := by
            have k_rat : (k : ℚ) < n + 1 := by linarith [hky1, hny2]
            exact_mod_cast k_rat
          exact Int.le_of_lt_add_one k_lt_n_plus_one
        --
        exact le_antisymm n_leq_k k_leq_n
      rw [n_eq_k] at hnx1 hnx2
      use k
