import Mathlib.Tactic.Have
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

lemma Set.union_inter_supset_left_of_disjoint {I₁ I₂ E₁ E₂ : Set α} (hE : E₁ ∩ E₂ = ∅) (hI : I₂ ⊆ E₂) :
    (I₁ ∪ I₂) ∩ E₁ = E₁ ∩ I₁ := by
  rw [Set.union_inter_distrib_right]
  conv => rhs; rw [Set.inter_comm]
  convert Set.union_empty _
  setesop

lemma Set.union_inter_supset_right_of_disjoint {I₁ I₂ E₁ E₂ : Set α} (hE : E₁ ∩ E₂ = ∅) (hI : I₁ ⊆ E₁) :
    (I₁ ∪ I₂) ∩ E₂ = E₂ ∩ I₂ := by
  rw [Set.union_comm]
  rw [Set.inter_comm] at hE
  exact Set.union_inter_supset_left_of_disjoint hE hI

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

lemma Set.union_inter_eq_fst {S₁ S₂ E₁ E₂ X₁ X₂ : Set α} (hE : E₁ ∩ E₂ = ∅) (hX₁ : S₁ ⊆ X₁ ∩ E₁) (hX₂ : S₂ ⊆ X₂ ∩ E₂) :
    (S₁ ∪ S₂) ∩ E₁ = S₁ := by
  rw [Set.union_inter_distrib_right]
  rw [Set.subset_inter_iff] at hX₁ hX₂
  convert Set.union_empty S₁
  · symm
    rw [Set.left_eq_inter]
    exact hX₁.right
  · rw [←Set.subset_empty_iff] at hE ⊢
    apply (Set.inter_subset_inter_left E₁ hX₂.right).trans
    rwa [Set.inter_comm] at hE

lemma Set.union_inter_eq_snd {S₁ S₂ E₁ E₂ X₁ X₂ : Set α} (hE : E₁ ∩ E₂ = ∅) (hX₁ : S₁ ⊆ X₁ ∩ E₁) (hX₂ : S₂ ⊆ X₂ ∩ E₂) :
    (S₁ ∪ S₂) ∩ E₂ = S₂ := by
  rw [Set.union_comm]
  rw [Set.inter_comm] at hE
  exact Set.union_inter_eq_fst hE hX₂ hX₁
