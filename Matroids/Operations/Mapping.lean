import Mathlib.Data.Matroid.IndepAxioms


def matroid_mapping {α β : Type*} (M' : IndepMatroid α) (f : α → β) : IndepMatroid β :=
  IndepMatroid.mk
    (f '' M'.E)
    (fun I : Set β => ∃ I' : Set α, M'.Indep I' ∧ f '' I' = I)
    ⟨∅, M'.indep_empty, Set.image_empty f⟩
    (by
      intro I J ⟨J', hJ', hfJ'⟩ hIinJ
      use J' ∩ f ⁻¹' I
      constructor
      · exact M'.indep_subset hJ' (by aesop)
      · rwa [Set.image_inter_preimage f J' I, hfJ', Set.inter_eq_right]
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
