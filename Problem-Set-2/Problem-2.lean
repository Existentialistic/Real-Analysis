import Mathlib.Tactic

variable {α β : Type}
variable {X A B : Set α}
variable {Y C D : Set β}
variable {f : α → β}
variable (hA : A ⊆ X) (hB : B ⊆ X)
variable (hC : C ⊆ Y) (hD : D ⊆ Y)

def image (f : α → β) (A : Set α) : Set β :=
  {y | ∃ x ∈ A, f x = y}

def preimage (f : α → β) (C : Set β) : Set α :=
  {x | f x ∈ C}

theorem union_of_preimages :
    preimage f (C ∪ D) = preimage f C ∪ preimage f D := by
  unfold preimage
  ext x
  rw [Set.mem_union]
  repeat rw [Set.mem_setOf_eq]
  repeat rw [Set.mem_union]

theorem intersection_of_preimages :
    preimage f (C ∩ D) = preimage f C ∩ preimage f D := by
  unfold preimage
  ext x
  rw [Set.mem_inter_iff]
  repeat rw [Set.mem_setOf_eq]
  rw [Set.mem_inter_iff]

theorem union_of_images :
    image f (A ∪ B) = image f A ∪ image f B := by
  unfold image
  ext y
  rw [Set.mem_union]
  repeat rw [Set.mem_setOf_eq]
  simp only [Set.mem_union]
  constructor
  · rintro ⟨x, (hxa | hxb), hfxy⟩
    · left; use x
    · right; use x
  · rintro (⟨x, hxa, hfxy⟩ | ⟨x, hxb, hfxy⟩)
    · use x; exact ⟨Or.inl hxa, hfxy⟩
    · use x; exact ⟨Or.inr hxb, hfxy⟩

theorem intersection_of_images :
    image f (A ∩ B) ⊆ image f A ∩ image f B := by
  unfold image
  intro y h
  rw [Set.mem_inter_iff]
  repeat rw [Set.mem_setOf_eq]
  rw [Set.mem_setOf_eq] at h
  simp only [Set.mem_inter_iff] at h
  obtain ⟨x, ⟨hxa, hxb⟩, hfx⟩ := h
  constructor <;> use x

theorem intersection_of_images_counterexample
    (a₁ a₂ : α) (b : β) (ha : a₁ ≠ a₂) :
    ∃ (f : α → β) (A : Set α) (B : Set α),
    image f (A ∩ B) ≠ image f A ∩ image f B := by
  set f : α → β := fun _ ↦ b with hf
  use f; use {a₁}; use {a₂}
  unfold image
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  simp only [↓existsAndEq, true_and]
  simp only [Set.setOf_eq_eq_singleton']
  rw [hf]
  simp only [Set.inter_self]
  simp only [ha, false_and]
  simp only [Set.setOf_false]
  exact Set.empty_ne_singleton b
