import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Tactic.Have


import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Data.Matrix.RowCol
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Tactic.Have

import Matroids.Automation.Tactics


def matroid_direct_sum {α: Type*} (M₁ M₂ : IndepMatroid α) (hME : M₁.E ∩ M₂.E = ∅) :=
  IndepMatroid.mk
    (M₁.E ∪ M₂.E)
    (fun I : Set α => ∃ I₁ I₂, I₁ ∪ I₂ = I ∧ M₁.Indep I₁ ∧ M₂.Indep I₂)
    ⟨∅, ∅, Set.union_self ∅, M₁.indep_empty, M₂.indep_empty⟩
    (fun A B ⟨B₁, B₂, hB, hB₁, hB₂⟩ hAB =>
      ⟨A ∩ B₁, A ∩ B₂, by aesop,
      M₁.indep_subset hB₁ (Set.inter_subset_right A B₁),
      M₂.indep_subset hB₂ (Set.inter_subset_right A B₂)⟩)
    (by
      intro I B ⟨I₁, I₂, hI, hI₁, hI₂⟩ hInimax hBinmax
      -- simp [maximals] at hInimax hBinmax
      obtain ⟨⟨B₁, B₂, hB₁₂, hB₁, hB₂⟩, hBnoext⟩ := hBinmax
      rw [← hI] at *
      clear hI I
      if hI₁nimax: I₁ ∉ maximals Set.Subset M₁.Indep then
        sorry
      else
        if hI₂nimax: I₂ ∉ maximals Set.Subset M₂.Indep then
          sorry
        else
          exfalso
          simp [maximals] at hInimax hI₁nimax hI₂nimax
          obtain ⟨X, hXI₂, hXI₁, X₁, X₂, hMIX₂, hMIX₁, hX, hhX⟩ := hInimax I₁ I₂ rfl hI₁ hI₂
          apply hhX
          have hX₁ : I₁ ⊆ X₁ := by
            simp only [← hX] at *
            have hcap₁ : I₁ ∩ X₂ = ∅ := (by
              apply M₁.subset_ground at hMIX₁
              apply M₂.subset_ground at hMIX₂
              apply M₁.subset_ground at hI₁
              clear * - hI₁ hMIX₁ hMIX₂ hME
              setauto
            )
            clear * - hcap₁ hXI₁
            intro a ha
            cases hXI₁ ha with
            | inl h => exact h
            | inr h =>
              exfalso
              have : a ∈ I₁ ∩ X₂ := ⟨ha, h⟩
              rw [hcap₁] at this
              simp at this
          have hX₂ : I₂ ⊆ X₂ := by
            simp only [← hX] at *
            have hcap₂ : I₂ ∩ X₁ = ∅ := (by
              apply M₁.subset_ground at hMIX₁
              apply M₂.subset_ground at hMIX₂
              apply M₂.subset_ground at hI₂
              clear * - hI₂ hMIX₁ hMIX₂ hME
              setauto
            )
            clear * - hcap₂ hXI₂
            intro a ha
            cases hXI₂ ha with
            | inl h =>
              exfalso
              have : a ∈ I₂ ∩ X₁ := ⟨ha, h⟩
              simp [hcap₂] at this
            | inr h => exact h
          rw [← hX]sorry hMIX₁ h
          | inr h =>
            right
            exact hI₂nimax.right X₂ hX₂ hMIX₂ h
    )
    (by
      intro X hX I ⟨I₁, I₂, hI₁₂, hI₁, hI₂⟩ hIX
      obtain ⟨T₁, hT₁⟩ := M₁.indep_maximal (X ∩ M₁.E) (by exact Set.inter_subset_right X M₁.E) I₁ hI₁ sorry
      obtain ⟨T₂, hT₂⟩ := M₂.indep_maximal (X ∩ M₂.E) (by exact Set.inter_subset_right X M₂.E) I₂ hI₂ sorry
      simp [maximals] at hT₁ hT₂ ⊢
      obtain ⟨⟨hindepT₁, hI₁subT₁, hT₁subX, hT₁subE⟩, hB₁⟩ := hT₁
      obtain ⟨⟨hindepT₂, hI₂subT₂, hT₂subX, hT₂subE⟩, hB₂⟩ := hT₂
      sorry
    )
    (by
      intro I hI
      obtain ⟨_, _, rfl, hM₁, hM₂⟩ := hI
      exact Set.union_subset_union (M₁.subset_ground _ hM₁) (M₂.subset_ground _ hM₂)
    )
