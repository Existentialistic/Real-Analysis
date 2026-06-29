import Mathlib.Tactic

variable (α : Type)
variable (A B X : Set α)
open Set

theorem set_theoretic_de_Morgan's_law : X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by
  ext x
  rw [mem_inter_iff]
  repeat rw [mem_diff]
  rw [mem_union]
  --Here we apply the boolean version of de-Morgan's law to ¬(x ∈ A ∨ x ∈ B)
  push Not
  --Now we have x ∈ X ∧ x ∉ A ∧ x ∉ B ↔ (x ∈ X ∧ x ∉ A) ∧ x ∈ X ∧ x ∉ B
  constructor
  · intro h
    match h with
    | ⟨hX, hnA, hnB⟩ => exact ⟨⟨hX, hnA⟩, hX, hnB⟩
  · intro h
    match h with
    | ⟨⟨hX, hnA⟩, _, hnB⟩ => exact ⟨hX, hnA, hnB⟩
