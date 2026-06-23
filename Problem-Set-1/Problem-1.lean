import Mathlib.Tactic.NthRewrite
open Int (add_comm add_assoc mul_comm mul_assoc mul_add add_mul mul_one one_mul add)

def type_1 (n : Int) : Prop :=
  ∃k : Int, n = 3*k + 1

def type_2 (n : Int) : Prop :=
  ∃k : Int, n = 3*k + 2

def type_3 (n : Int) : Prop :=
  ∃k : Int, n = 3*k + 3

theorem type1_plus_type1 (h1 : type_1 a) (h2 : type_1 b) : type_2 (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2, by
    rw [hw1, hw2]
    rw [add_assoc, add_comm 1]
    rw [add_assoc (3 * w2) _ _]
    rw [← add_assoc (3 * w1) _ _]
    rw [← mul_add]
    rfl⟩

theorem type1_plus_type2 (h1 : type_1 a) (h2 : type_2 b) : type_3 (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2, by
    rw [hw1, hw2]
    rw [add_assoc, add_comm 1]
    rw [add_assoc (3 * w2) _ _]
    rw [← add_assoc (3 * w1) _ _]
    rw [← mul_add]
    rfl⟩

theorem type1_plus_type3 (h1 : type_1 a) (h2 : type_3 b) : type_1 (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2 + 1, by
    rw [hw1, hw2]
    rw [add_assoc, add_comm 1]
    rw [add_assoc (3 * w2) _ _]
    rw [← add_assoc (3 * w1) _ _]
    rw [← mul_add]
    rw [← add_assoc]
    nth_rw 2 [←  mul_one 3]
    rw [← mul_add 3]⟩

theorem type2_plus_type2 (h1 : type_2 a) (h2 : type_2 b) : type_1 (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2 + 1, by
    rw [hw1, hw2]
    rw [add_assoc, add_comm 2]
    rw [add_assoc (3 * w2) _ _]
    rw [← add_assoc (3 * w1) _ _]
    rw [← mul_add]
    have h3 : (2 : Int) + (2 : Int) = (3 : Int) + (1 : Int) := rfl
    rw [h3]
    rw [← add_assoc]
    nth_rw 2 [←  mul_one 3]
    rw [← mul_add 3]⟩

theorem type2_plus_type3 (h1 : type_2 a) (h2 : type_3 b) : type_2 (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2 + 1, by
    rw [hw1, hw2]
    rw [add_assoc, add_comm 2]
    rw [add_assoc (3 * w2) _ _]
    rw [← add_assoc (3 * w1) _ _]
    rw [← mul_add]
    rw [← add_assoc]
    nth_rw 2 [←  mul_one 3]
    rw [← mul_add 3]⟩

theorem type3_plus_type3 (h1 : type_3 a) (h2 : type_3 b) : type_3 (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2 + 1, by
    rw [hw1, hw2]
    rw [add_assoc, add_comm 3]
    rw [add_assoc (3 * w2) _ _]
    rw [← add_assoc (3 * w1) _ _]
    rw [← mul_add]
    rw [← add_assoc]
    nth_rw 2 [←  mul_one 3]
    rw [← mul_add 3]⟩

theorem type1_times_type1 (h1 : type_1 a) (h2 : type_1 b) : type_1 (a * b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
  ⟨(w1 * (3 * w2 + 1) + w2), by
  rw [hw1, hw2]
  rw [add_mul]
  rw [one_mul]
  rw [← add_assoc]
  rw [mul_assoc]
  rw [← mul_add 3]⟩

theorem type1_times_type2 (h1 : type_1 a) (h2 : type_2 b) : type_2 (a * b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
  ⟨(w1 * (3 * w2 + 2) + w2), by
  rw [hw1, hw2]
  rw [add_mul]
  rw [one_mul]
  rw [← add_assoc]
  rw [mul_assoc]
  rw [← mul_add 3]⟩

theorem type1_times_type3 (h1 : type_1 a) (h2 : type_3 b) : type_3 (a * b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
  ⟨(w1 * (3 * w2 + 3) + w2), by
  rw [hw1, hw2]
  rw [add_mul]
  rw [one_mul]
  rw [← add_assoc]
  rw [mul_assoc]
  rw [← mul_add 3]⟩

theorem type2_times_type2 (h1 : type_2 a) (h2 : type_2 b) : type_1 (a * b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
  ⟨(w1 * (3 * w2 + 2) + (2 * w2 + 1)), by
  rw [hw1, hw2]
  rw [add_mul]
  nth_rw 2 [mul_add]
  rw [← mul_assoc 2 3 _]
  rw [mul_comm 2 3]
  have h3 : (2 : Int) * (2 : Int) = (3 : Int) * (1 : Int) + (1 : Int) := rfl
  rw [h3]
  rw [mul_assoc 3 2 _]
  rw [← add_assoc _ _ 1]
  rw [← mul_add 3]
  rw [← add_assoc]
  rw [mul_assoc]
  rw [← mul_add 3]⟩

theorem type2_times_type3 (h1 : type_2 a) (h2 : type_3 b) : type_3 (a * b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
  ⟨(w1 * (3 * w2 + 3) + (2 * w2 + 1)), by
  rw [hw1, hw2]
  rw [add_mul]
  nth_rw 2 [mul_add]
  rw [← mul_assoc 2 3 _]
  rw [mul_comm 2 3]
  have h3 : (3 : Int) * (2 : Int) = (3 : Int) * (1 : Int) + (3 : Int) := rfl
  nth_rw 2 [h3]
  rw [mul_assoc 3 2 _]
  rw [← add_assoc _ _ 3]
  rw [← mul_add 3]
  rw [← add_assoc]
  rw [mul_assoc]
  rw [← mul_add 3]⟩

theorem type3_times_type3 (h1 : type_3 a) (h2 : type_3 b) : type_3 (a * b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
  ⟨(w1 * (3 * w2 + 3) + (3 * w2 + 2)), by
  rw [hw1, hw2]
  rw [add_mul]
  nth_rw 2 [mul_add]
  rw [← mul_assoc 3 3 _]
  rw [mul_comm 3 3]
  have h3 : (3 : Int) * (3 : Int) = (3 : Int) * (2 : Int) + (3 : Int) := rfl
  nth_rw 2 [h3]
  rw [mul_assoc 3 3 _]
  rw [← add_assoc _ _ 3]
  rw [← mul_add 3]
  rw [← add_assoc]
  rw [mul_assoc]
  rw [← mul_add 3]⟩
