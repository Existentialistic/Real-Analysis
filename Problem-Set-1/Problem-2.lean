import Mathlib.Data.Int.Basic
import Mathlib.Tactic

def type_1 (n : Int) : Prop :=
  ∃k : Int, n = 3*k + 1

def type_2 (n : Int) : Prop :=
  ∃k : Int, n = 3*k + 2

def type_3 (n : Int) : Prop :=
  ∃k : Int, n = 3*k + 3

theorem every_int_even_or_odd : ∀n : Int, Even n ∨ Odd n :=
  fun n => by
    cases n with
    | ofNat n =>
      induction n with
      | zero =>
        left
        match 0 with
        | w1 =>
          use 0
          rfl
      | succ n ih =>
          cases ih with
          | inl ha =>
            right
            obtain ⟨k, hk⟩ := ha
            use k
            grind
          | inr hb =>
            left
            obtain ⟨k, hk⟩ := hb
            use k + 1
            grind
    | negSucc n =>
      induction n with
      | zero =>
        right
        match 0 with
        | w1 =>
          use -1
          grind
      | succ n ih =>
        cases ih with
        | inl ha =>
          right
          obtain ⟨k, hk⟩ := ha
          use k - 1
          grind
        | inr hb =>
          left
          obtain ⟨k, hk⟩ := hb
          use k
          grind

theorem every_int_type1_type2_or_type3 :
        ∀n : Int, type_1 n ∨ type_2 n ∨ type_3 n :=
  fun n => by
    cases n with
    | ofNat n =>
     induction n with
      | zero =>
        right
        right
        match 0 with
        | w1 =>
          use -1
          rfl
      | succ n ih =>
        cases ih with
        | inl ha =>
          right
          left
          obtain ⟨k, hk⟩ := ha
          use k
          grind
        | inr hbc =>
          cases hbc with
          | inl hb =>
            right
            right
            obtain ⟨k, hk⟩ := hb
            use k
            grind
          | inr hc =>
            left
            obtain ⟨k, hk⟩ := hc
            use k + 1
            grind
    | negSucc n =>
      induction n with
      | zero =>
        right
        left
        match 0 with
        | w1 =>
          use -1
          rfl
      | succ n ih =>
        cases ih with
        | inl ha =>
          right
          right
          obtain ⟨k, hk⟩ := ha
          use k - 1
          grind
        | inr hbc =>
          cases hbc with
          | inl hb =>
            left
            obtain ⟨k, hk⟩ := hb
            use k
            grind
          | inr hc =>
            right
            left
            obtain ⟨k, hk⟩ := hc
            use k
            grind
