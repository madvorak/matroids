import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Tactic.Have


def matroid_intersection {α : Type*} {M₁ M₂ : IndepMatroid α} (hME : M₁.E = M₂.E) :=
  IndepMatroid.mk
    M₁.E
    (fun S : Set α => M₁.Indep S ∧ M₂.Indep S)
    ⟨M₁.indep_empty, M₂.indep_empty⟩
    (fun _ _ ⟨hM₁, hM₂⟩ hIJ =>
       ⟨M₁.indep_subset hM₁ hIJ, M₂.indep_subset hM₂ hIJ⟩)
    (by
      intro I B ⟨hM₁, hM₂⟩ hIni hBin
      have hhM₁ := M₁.indep_aug
      have hhM₂ := M₂.indep_aug
      simp [maximals] at *
      obtain ⟨⟨hB₁, hB₂⟩, hBb⟩ := hBin
      obtain ⟨x₁, ⟨hBx₁, hIx₁⟩, hMx₁⟩ := hhM₁ hM₁ sorry hB₁ sorry
      obtain ⟨x₂, ⟨hBx₂, hIx₂⟩, hMx₂⟩ := hhM₂ hM₂ sorry hB₂ sorry
      sorry
    )
    (by
      intro X hX
      obtain hM₁ := M₁.indep_maximal X hX
      obtain hM₂ := M₂.indep_maximal X (hME ▸ hX)
      by_contra contr
      simp [Matroid.ExistsMaximalSubsetProperty] at *
      obtain ⟨Y, hYX, hM₂Y, hM₁Y, hY⟩ := contr
      simp only [Set.Nonempty] at hY
      apply hY
      clear hY
      obtain ⟨Y₁, hY₁⟩ := hM₁ Y hM₁Y hYX
      obtain ⟨Y₂, hY₂⟩ := hM₂ Y hM₂Y hYX
      use Y₁ ∩ Y₂
      simp [maximals] at *
      obtain ⟨⟨hM₁Y₁, hYY₁, hY₁X⟩, hB₁⟩ := hY₁
      obtain ⟨⟨hM₂Y₂, hYY₂, hY₂X⟩, hB₂⟩ := hY₂
      constructor
      · constructor
        · constructor
          · exact M₁.indep_subset hM₁Y₁ (Set.inter_subset_left Y₁ Y₂)
          · exact M₂.indep_subset hM₂Y₂ (Set.inter_subset_right Y₁ Y₂)
        · refine ⟨⟨hYY₁, hYY₂⟩, ?_⟩
          intro a ha
          exact hY₁X ha.left
      · intro B hM₁B hM₂B hYB hBX hYYB
        constructor
        · apply hB₁ hM₁B hYB hBX
          intro b hb
          apply hYYB
          refine ⟨hb, ?_⟩
          apply hB₂ hM₂B hYB hBX
          sorry
          sorry
        sorry
    )
    (fun _ ⟨hM₁, _⟩ => M₁.subset_ground _ hM₁)
