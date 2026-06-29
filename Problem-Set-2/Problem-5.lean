import Mathlib.Tactic


variable (α : Type)

def reflexive (α : Type) (r : α → α → Prop) : Prop :=
  (∀ x, r x x)

def symmetric (α : Type) (r : α → α → Prop) : Prop :=
  (∀ x y, r x y ↔ r y x)

def transitive (α : Type) (r : α → α → Prop) : Prop :=
  (∀ x y z, r x y → r y z → r x z)

def equivalence (α : Type) (r : α → α → Prop) : Prop :=
  reflexive α r ∧ symmetric α r ∧ transitive α r


def non_empty (α : Type) (P : Set (Set α)) : Prop :=
  ∀ A ∈ P, A ≠ ∅

def disjoint (α : Type) (P : Set (Set α)) : Prop :=
  ∀ A₁ ∈ P, ∀ A₂ ∈ P, A₁ ≠ A₂ → A₁ ∩ A₂ = ∅

def union_cover (α : Type) (P : Set (Set α)) : Prop :=
  ⋃₀ P = Set.univ

def partition (α : Type) (P : Set (Set α)) : Prop :=
  non_empty α P ∧ disjoint α P ∧ union_cover α P


def equivalence_class (α : Type) (x : α) (r : α → α → Prop)
    (_ : equivalence α r) : Set α :=
  {y : α | r x y}

def P_E (α : Type) (r : α → α → Prop)
    (he : equivalence α r) : Set (Set α) :=
  {A : Set α | ∃ (x : α), A = equivalence_class α x r he}

def E_P (α : Type) (P : Set (Set α))
    (_ : partition α P) : (α → α → Prop) :=
  fun x y => ∃ A ∈ P, x ∈ A ∧ y ∈ A


theorem PE_is_partition (α : Type) (r : α → α → Prop) (he : equivalence α r) :
    partition α (P_E α r he) := by
  unfold partition
  unfold equivalence at he
  unfold reflexive symmetric transitive at he
  rcases he with ⟨ref, sym, tran⟩
  constructor
  · unfold non_empty
    unfold P_E
    intro A
    simp only [Set.mem_setOf_eq, ne_eq, forall_exists_index]
    intro x
    unfold equivalence_class
    intro hA
    have rxx : r x x := ref x
    have x_mem_A : x ∈ A := by
      rw [hA]
      simp only [Set.mem_setOf_eq]
      exact rxx
    intro A_empty
    rw [A_empty] at x_mem_A
    exact x_mem_A
  · constructor
    · unfold disjoint P_E equivalence_class
      simp only [Set.mem_setOf_eq, ne_eq, forall_exists_index]
      intro A₁ x hA₁ A₂ y hA₂ A₁_neq_A₂
      ext z
      rw [hA₁, hA₂]
      constructor
      · rw [Set.mem_inter_iff]
        simp only [Set.mem_setOf_eq]
        intro ⟨rxz, ryz⟩
        simp only [Set.mem_empty_iff_false]
        have rzy := (sym y z).mp ryz
        have rxy := tran x z y rxz rzy
        have ryx := (sym x y).mp rxy
        have A₁_eq_A₂ : A₁ = A₂ := by
          ext k
          rw [hA₁, hA₂]
          simp only [Set.mem_setOf_eq]
          constructor
          · intro rxk
            apply tran y x k ryx rxk
          · intro ryk
            apply tran x y k rxy ryk
        contradiction
      · simp only [Set.mem_empty_iff_false]
        exact fun h => False.elim h
    · unfold union_cover P_E equivalence_class
      ext y
      simp only [Set.mem_sUnion, Set.mem_setOf_eq, ↓existsAndEq, true_and]
      constructor
      · intro ⟨x, hx⟩
        apply Set.mem_univ
      · intro hy
        use y
        exact ref y

theorem EP_is_equivalence (α : Type) (P : Set (Set α)) (hp : partition α P) :
    equivalence α (E_P α P hp) := by
  unfold partition at hp
  unfold non_empty disjoint union_cover at hp
  rcases hp with ⟨nepty, dsj, ucver⟩
  unfold equivalence
  constructor
  · unfold reflexive
    intro x
    unfold E_P
    have x_mem_up : x ∈ ⋃₀ P := by rw [ucver]; apply Set.mem_univ
    rw [Set.mem_sUnion] at x_mem_up
    obtain ⟨A, hA⟩ := x_mem_up
    use A
    norm_num
    exact hA
  · constructor
    · unfold symmetric
      intro x y
      unfold E_P
      conv =>
        lhs; rhs;
        intro A
        rhs;
        rw [and_comm ]
    · unfold transitive
      intro x y z
      unfold E_P
      intro ⟨A₁, ⟨hA₁, hx, hy1⟩⟩ ⟨A₂, ⟨hA₂, hy2, hz⟩⟩
      have inter_not_empty : A₁ ∩ A₂ ≠ ∅ := by
        intro inter_empty
        have y_in_inter : y ∈ A₁ ∩ A₂ := by exact ⟨hy1, hy2⟩
        rw [inter_empty] at y_in_inter
        contradiction
      have A₁_eq_A₂ : A₁ = A₂ := by
        by_contra A₁_neq_A₂
        have inter_empty := dsj A₁ hA₁ A₂ hA₂ A₁_neq_A₂
        contradiction
      use A₁
      exact ⟨hA₁, hx, by rw [A₁_eq_A₂]; exact hz⟩

theorem EP_PE_eq_E (α : Type) (r : α → α → Prop) (he : equivalence α r) :
    E_P α (P_E α r he) (PE_is_partition α r he) = (fun x y => r x y) := by
  unfold E_P P_E equivalence_class
  unfold equivalence at he
  rcases he with ⟨refl, symm, trans⟩
  simp only [ Set.mem_setOf_eq, ↓existsAndEq, true_and]
  funext x y
  conv => lhs; rhs; intro z
  simp only [eq_iff_iff]
  constructor
  · intro z
    obtain ⟨z, rzx, rzy⟩ := z
    exact trans ↑x z ↑y ((symm z x).mp rzx) rzy
  · intro rxy
    use x
    exact ⟨refl x, rxy⟩

theorem PE_EP_eq_P (α : Type) (P : Set (Set α)) (hp : partition α P) :
    P_E α (E_P α P hp) (EP_is_equivalence α P hp) = P := by
  unfold E_P P_E equivalence_class
  rcases hp with ⟨nempty, dsjnt, u_cover⟩
  unfold non_empty at nempty
  unfold disjoint at dsjnt
  unfold union_cover at u_cover
  simp only
  ext A
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    obtain ⟨x, hx⟩ := hx
    rw [hx]
    have x_mem_up: x ∈ ⋃₀ P := by rw [u_cover]; apply Set.mem_univ
    simp only [Set.mem_sUnion] at x_mem_up
    obtain ⟨A, hAP, hxA⟩ := x_mem_up
    have : {y | ∃ A ∈ P, x ∈ A ∧ y ∈ A} = A := by
      ext y
      simp only [Set.mem_setOf_eq]
      constructor
      · intro temp
        obtain ⟨B, hBP, hxB, hyB⟩ := temp
        have hxAB : x ∈ A ∩ B := ⟨hxA, hxB⟩
        have A_eq_B : A = B := by
          by_contra A_neq_B
          push Not at A_neq_B
          have A_inter_B_empty := dsjnt A hAP B hBP A_neq_B
          rw [A_inter_B_empty] at hxAB
          exact hxAB
        rw [A_eq_B]
        exact hyB
      · intro hyA
        use A
    rw [this]
    exact hAP
  · intro hAP
    have A_nempty := nempty A hAP
    have x_exists : ∃ x, x ∈ A := by
      by_contra
      simp only [not_exists] at this
      have A_empty : A = ∅ := by
        ext x
        have x_nmem_A := this x
        simp only [Set.mem_empty_iff_false, iff_false]
        exact x_nmem_A
      exact absurd A_empty A_nempty
    obtain ⟨x, hxA⟩ := x_exists
    use x
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hyA
      use A
    · intro this
      obtain ⟨B, hBP, hxB, hyB⟩ := this
      have hxAB : x ∈ A ∩ B := ⟨hxA, hxB⟩
      have A_eq_B : A = B := by
        by_contra A_neq_B
        push Not at A_neq_B
        have A_inter_B_empty := dsjnt A hAP B hBP A_neq_B
        rw [A_inter_B_empty] at hxAB
        exact hxAB
      rw [A_eq_B]
      exact hyB
