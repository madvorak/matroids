import Mathlib.Data.Matroid.IndepAxioms


def matroid_mapping {α β: Type*} (M' : IndepMatroid α) (f : α → β) :=
  IndepMatroid.mk
    (f '' M'.E)
    (fun I : Set β => ∃ I', M'.Indep I' ∧ f '' I' = I)
    ⟨∅, M'.indep_empty, Set.image_empty f⟩
    (by
      intro I J hJ hIinJ
      obtain ⟨J', hJ', hfJ'⟩ := hJ
      existsi J' ∩ f ⁻¹' I

      constructor
      case left =>
        have hInter : (J' ∩ f ⁻¹' I ⊆ J') := by aesop
        exact M'.indep_subset hJ' hInter
      case right =>
        rw [Set.image_inter_preimage f J' I, hfJ', Set.inter_eq_right]
        exact hIinJ
    )
    (by
      sorry
    )
    (by
      intro X hX
      unfold Matroid.ExistsMaximalSubsetProperty
      intro I' hI' hI'subset
      obtain ⟨I, hI, hfI⟩ := hI'
      unfold Set.Nonempty maximals
      simp
      sorry
    )
    (by
      intro I hI
      obtain ⟨I', hI', hfI'⟩ := hI
      rw [← hfI']
      apply M'.subset_ground at hI'
      exact Set.image_subset f hI'
    )
