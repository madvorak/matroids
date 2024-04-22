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
  · intro ⟨hE₁, hE₂⟩ x
    setauto
    specialize hA x
    specialize hE₁ x
    specialize hE₂ x
    tauto

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

lemma Set.chain_to_components {E₁ E₂ I T X : Set α}
     (hIT : I ⊆ T) (hTX : T ⊆ X) :
    ((I ∩ E₁) ⊆ (T ∩ E₁) ∧ (T ∩ E₁) ⊆ (X ∩ E₁)) ∧
    ((I ∩ E₂) ⊆ (T ∩ E₂) ∧ (T ∩ E₂) ⊆ (X ∩ E₂)) := by
  setauto
