import Mathlib.Tactic
import Mathlib.Data.Set.Basic

open BigOperators
open Finset
open List
open Set


def polynomial (coefs : List ℚ) : ℝ → ℝ :=
  fun x =>
    ∑ i ∈ Finset.range coefs.length, coefs[i]! * x^i

def 𝔸 : Set ℝ :=
  {x : ℝ | ∃ coefs : List ℚ, coefs ≠ [] ∧ polynomial coefs x = 0}

def injective (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

def surjective (f : α → β) : Prop :=
  ∀ y : β, ∃ x : α, f x = y

def bijective (f : α → β) : Prop :=
  injective f ∧ surjective f

def my_countable (X : Set α) : Prop :=
  ∃ f : X → ℕ, bijective f

--Too difficult, may attempt later.
theorem 𝔸_countable : my_countable 𝔸 := by
  sorry

def my_product (X : Set α) (Y : Set β) : Set (α × β) :=
  {p | p.fst ∈ X ∧ p.snd ∈ Y}

def cantor_pairing_fun (X : Set α) (Y : Set β)
      (hX : my_countable X) (hY : my_countable Y) : my_product X Y → ℕ :=
  fun prod => by
    unfold my_countable bijective injective surjective at *
    exact sorry

--Countable Product of Countable Sets is Countable
lemma CPCSC (X : Set α) (Y : Set β)
      (hX : my_countable X) (hY : my_countable Y) :
      my_countable (my_product X Y) := by
  unfold my_countable bijective injective surjective at hX
  unfold my_countable bijective injective surjective at hY
  unfold my_countable bijective injective surjective
  sorry
