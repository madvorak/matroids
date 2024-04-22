import Matroids.Utilities.Tactics

variable {α : Type*}


lemma Set.eq_union_inters_of_disjoint {A B C : Set α} (hA : A ⊆ B ∪ C) :
    A = A ∩ B ∪ A ∩ C := by
  aesop

lemma Set.subset_inter_of_redundant_right {A B C D : Set α} (hAB : A ∪ D ⊆ B) (hBC : A ⊆ C) :
    A ⊆ B ∩ C :=
  Set.subset_inter ((Set.subset_union_left A D).trans hAB) hBC

lemma Set.subset_inter_of_redundant_left {A B C D : Set α} (hAB : D ∪ A ⊆ B) (hBC : A ⊆ C) :
    A ⊆ B ∩ C :=
  Set.subset_inter ((Set.subset_union_right D A).trans hAB) hBC

lemma Set.subset_iff_subsets_of_disjoint {A B E₁ E₂ : Set α} (hA : A ⊆ E₁ ∪ E₂) :
    A ⊆ B ↔ A ∩ E₁ ⊆ B ∩ E₁ ∧ A ∩ E₂ ⊆ B ∩ E₂ := by
  constructor
  · setauto
  · intro ⟨hABE₁, hABE₂⟩ x hx
    setauto
    cases hA x hx with
    | inl hE₁ => exact (hABE₁ x ⟨hx, hE₁⟩).left
    | inr hE₁ => exact (hABE₂ x ⟨hx, hE₁⟩).left

lemma Set.strict_subsets_of_disjoint {A B E₁ E₂ : Set α}
    (hA : A ⊆ E₁ ∪ E₂) (hB : B ⊆ E₁ ∪ E₂) (hE : E₁ ∩ E₂ = ∅) (hAB : A ⊂ B) :
    A ∩ E₁ ⊂ B ∩ E₁ ∨ A ∩ E₂ ⊂ B ∩ E₂ := by
  obtain ⟨_, hBA⟩ := hAB
  rw [Set.not_subset] at hBA
  obtain ⟨a, _, _⟩ := hBA
  if ha : a ∈ E₁ ∪ E₂ then
    cases ha with
    | inl =>
      left
      constructor
      · setauto
      · setesop
    | inr =>
      right
      constructor
      · setauto
      · setesop
  else
    tauto

lemma Set.between_inter {I T X : Set α} (hIT : I ⊆ T) (hTX : T ⊆ X) (E : Set α) :
    (I ∩ E) ⊆ (T ∩ E) ∧ (T ∩ E) ⊆ (X ∩ E) :=
  ⟨Set.inter_subset_inter_left E hIT, Set.inter_subset_inter_left E hTX⟩
