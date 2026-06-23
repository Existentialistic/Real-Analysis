import Mathlib.Tactic

theorem sqrt_3_irrational : Irrational (Real.sqrt 3) := by
  rw [irrational_iff_ne_rational]
  intro a b b_neq_zero
  change (√3 = ↑a / ↑b) → False
  intro sqrt_3_rational
  set q := Rat.divInt a b with hq
  obtain ⟨num, den, b_neq_zero, coprime⟩ := q
  --
  have reduced_fraction : √3 = num / den := by
    rw [sqrt_3_rational]
    have Rat_divInt_cast : (↑a : Real) / (↑b : Real) = Rat.divInt a b := by
      exact Eq.symm (Rat.cast_divInt a b)
    rw [Rat_divInt_cast]
    rw [← hq]
    exact Rat.cast_mk' num den b_neq_zero coprime
  apply_fun (· * ↑den) at reduced_fraction
  field_simp at reduced_fraction
  apply_fun (· ^ 2) at reduced_fraction
  field_simp at reduced_fraction
  have : √3 ^ 2 = 3 := by apply Real.sq_sqrt; grind
  rw [this] at reduced_fraction
  --
  have three_dvd_num_sq : num ^ 2 % 3 = 0 := by
    suffices 3 ∣ num^2 by exact Int.emod_eq_zero_of_dvd this
    use den ^ 2
    rify
    exact Eq.symm reduced_fraction
  have three_dvd_num : num % 3 = 0 := by
    have : num % 3 = 0 ∨ num % 3 = 1 ∨ num % 3 = 2 := by omega
    rcases this with h0 | h1 | h2
    case inl h0 => assumption
    case inr.inl h1 =>
      rw [pow_two] at three_dvd_num_sq
      rw [Int.mul_emod] at three_dvd_num_sq
      rw [h1] at three_dvd_num_sq
      omega
    case inr.inr h2 =>
      rw [pow_two] at three_dvd_num_sq
      rw [Int.mul_emod] at three_dvd_num_sq
      rw [h2] at three_dvd_num_sq
      omega
  have : ∃ k, num = 3 * k := by use num / 3; omega
  obtain ⟨k, hk⟩ := this
  rw [hk] at reduced_fraction
  rify at reduced_fraction
  rw [mul_pow] at reduced_fraction
  field_simp at reduced_fraction
  have three_dvd_den_sq : den ^ 2 % 3 = 0 := by
    suffices 3 ∣ den^2 by exact Nat.mod_eq_zero_of_dvd this
    rify
    use ↑k ^ 2
    rify
    exact Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (id (Eq.symm reduced_fraction))))
  have three_dvd_den : den % 3 = 0 := by
    have : den % 3 = 0 ∨ den % 3 = 1 ∨ den % 3 = 2 := by omega
    rcases this with h0 | h1 | h2
    case inl h0 => assumption
    case inr.inl h1 =>
      rw [pow_two] at three_dvd_den_sq
      rw [Nat.mul_mod] at three_dvd_den_sq
      rw [h1] at three_dvd_den_sq
      omega
    case inr.inr h2 =>
      rw [pow_two] at three_dvd_den_sq
      rw [Nat.mul_mod] at three_dvd_den_sq
      rw [h2] at three_dvd_den_sq
      omega
  apply Int.dvd_of_emod_eq_zero at three_dvd_num
  apply Nat.dvd_of_mod_eq_zero at three_dvd_den
  have three_dvd_num_nat : 3 ∣ num.natAbs := by exact Int.ofNat_dvd_left.mp three_dvd_num
  have three_dvd_gcd : 3 ∣ Nat.gcd num.natAbs den := by
    exact Nat.dvd_gcd three_dvd_num_nat three_dvd_den
  omega

theorem sqrt_5_irrational : Irrational (Real.sqrt 5) := by
  rw [irrational_iff_ne_rational]
  intro a b b_neq_zero
  change (√5 = ↑a / ↑b) → False
  intro sqrt_5_rational
  set q := Rat.divInt a b with hq
  obtain ⟨num, den, b_neq_zero, coprime⟩ := q
  --
  have reduced_fraction : √5 = num / den := by
    rw [sqrt_5_rational]
    have Rat_divInt_cast : (↑a : Real) / (↑b : Real) = Rat.divInt a b := by
      exact Eq.symm (Rat.cast_divInt a b)
    rw [Rat_divInt_cast]
    rw [← hq]
    exact Rat.cast_mk' num den b_neq_zero coprime
  apply_fun (· * ↑den) at reduced_fraction
  field_simp at reduced_fraction
  apply_fun (· ^ 2) at reduced_fraction
  field_simp at reduced_fraction
  have : √5 ^ 2 = 5 := by apply Real.sq_sqrt; grind
  rw [this] at reduced_fraction
  --
  have five_dvd_num_sq : num ^ 2 % 5 = 0 := by
    suffices 5 ∣ num^2 by exact Int.emod_eq_zero_of_dvd this
    use den ^ 2
    rify
    exact Eq.symm reduced_fraction
  have five_dvd_num : num % 5 = 0 := by
    have : num % 5 = 0 ∨ num % 5 = 1 ∨ num % 5 = 2 ∨ num % 5 = 3 ∨ num % 5 = 4 :=
      by omega
    rcases this with h0 | h1 | h2 | h3 | h4
    case inl h0 => assumption
    case inr.inl h1 =>
      rw [pow_two] at five_dvd_num_sq
      rw [Int.mul_emod] at five_dvd_num_sq
      rw [h1] at five_dvd_num_sq
      omega
    case inr.inr.inl h2 =>
      rw [pow_two] at five_dvd_num_sq
      rw [Int.mul_emod] at five_dvd_num_sq
      rw [h2] at five_dvd_num_sq
      omega
    case inr.inr.inr.inl h3 =>
      rw [pow_two] at five_dvd_num_sq
      rw [Int.mul_emod] at five_dvd_num_sq
      rw [h3] at five_dvd_num_sq
      omega
    case inr.inr.inr.inr h4 =>
      rw [pow_two] at five_dvd_num_sq
      rw [Int.mul_emod] at five_dvd_num_sq
      rw [h4] at five_dvd_num_sq
      omega
  have : ∃ k, num = 5 * k := by use num / 5; omega
  obtain ⟨k, hk⟩ := this
  rw [hk] at reduced_fraction
  rify at reduced_fraction
  rw [mul_pow] at reduced_fraction
  field_simp at reduced_fraction
  have five_dvd_den_sq : den ^ 2 % 5 = 0 := by
    suffices 5 ∣ den^2 by exact Nat.mod_eq_zero_of_dvd this
    rify
    use ↑k ^ 2
    rify
    exact Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (id (Eq.symm reduced_fraction))))
  have five_dvd_den : den % 5 = 0 := by
    have : den % 5 = 0 ∨ den % 5 = 1 ∨ den % 5 = 2 ∨ den % 5 = 3 ∨ den % 5 = 4 :=
      by omega
    rcases this with h0 | h1 | h2 | h3 | h4
    case inl h0 => assumption
    case inr.inl h1 =>
      rw [pow_two] at five_dvd_den_sq
      rw [Nat.mul_mod] at five_dvd_den_sq
      rw [h1] at five_dvd_den_sq
      omega
    case inr.inr.inl h2 =>
      rw [pow_two] at five_dvd_den_sq
      rw [Nat.mul_mod] at five_dvd_den_sq
      rw [h2] at five_dvd_den_sq
      omega
    case inr.inr.inr.inl h3 =>
      rw [pow_two] at five_dvd_den_sq
      rw [Nat.mul_mod] at five_dvd_den_sq
      rw [h3] at five_dvd_den_sq
      omega
    case inr.inr.inr.inr h4 =>
      rw [pow_two] at five_dvd_den_sq
      rw [Nat.mul_mod] at five_dvd_den_sq
      rw [h4] at five_dvd_den_sq
      omega
  apply Int.dvd_of_emod_eq_zero at five_dvd_num
  apply Nat.dvd_of_mod_eq_zero at five_dvd_den
  have five_dvd_num_nat : 5 ∣ num.natAbs := by exact Int.ofNat_dvd_left.mp five_dvd_num
  have five_dvd_gcd : 5 ∣ Nat.gcd num.natAbs den := by
    exact Nat.dvd_gcd five_dvd_num_nat five_dvd_den
  omega

theorem sqrt_4_irrational : Irrational (Real.sqrt 4) := by
  rw [irrational_iff_ne_rational]
  intro a b b_neq_zero
  change (√4 = ↑a / ↑b) → False
  intro sqrt_4_rational
  set q := Rat.divInt a b with hq
  obtain ⟨num, den, b_neq_zero, coprime⟩ := q
  --
  have reduced_fraction : √4 = num / den := by
    rw [sqrt_4_rational]
    have Rat_divInt_cast : (↑a : Real) / (↑b : Real) = Rat.divInt a b := by
      exact Eq.symm (Rat.cast_divInt a b)
    rw [Rat_divInt_cast]
    rw [← hq]
    exact Rat.cast_mk' num den b_neq_zero coprime
  apply_fun (· * ↑den) at reduced_fraction
  field_simp at reduced_fraction
  apply_fun (· ^ 2) at reduced_fraction
  field_simp at reduced_fraction
  have : √4 ^ 2 = 4 := by apply Real.sq_sqrt; grind
  rw [this] at reduced_fraction
  --
  have four_dvd_num_sq : num ^ 2 % 4 = 0 := by
    suffices 4 ∣ num^2 by exact Int.emod_eq_zero_of_dvd this
    use den ^ 2
    rify
    exact Eq.symm reduced_fraction
  --The proof fails here because we can't derive a contradiction from n = 2 mod 4. We know that n^2
  --= 0 mod 4 but this equation has two solutions, namely n = 0 mod 4 and n = 2 mod 4. For √5 and √3
  --we had unique solutions for n = 0 mod 5 or mod 3
  have four_dvd_num : num % 4 = 0 := by
    have : num % 4 = 0 ∨ num % 4 = 1 ∨ num % 4 = 2 ∨ num % 4 = 3 :=
      by omega
    rcases this with h0 | h1 | h2 | h3
    case inl h0 => assumption
    case inr.inl h1 =>
      rw [pow_two] at four_dvd_num_sq
      rw [Int.mul_emod] at four_dvd_num_sq
      rw [h1] at four_dvd_num_sq
      omega
    case inr.inr.inl h2 =>
      rw [pow_two] at four_dvd_num_sq
      rw [Int.mul_emod] at four_dvd_num_sq
      rw [h2] at four_dvd_num_sq
      --Here we have 2 * 2 % 4 = 0, which is true, so the omega tactic fails to derive a
      --contradiction from it
      --omega
      sorry
    case inr.inr.inr h3 =>
      rw [pow_two] at four_dvd_num_sq
      rw [Int.mul_emod] at four_dvd_num_sq
      rw [h3] at four_dvd_num_sq
      omega
  sorry
