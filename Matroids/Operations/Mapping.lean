import Mathlib.Data.Matroid.IndepAxioms


def indepMatroidMapping {α β : Type*} (M' : IndepMatroid α) (f : α → β) : IndepMatroid β :=
  IndepMatroid.mk
    (f '' M'.E)
    (fun I : Set β => ∃ I' : Set α, M'.Indep I' ∧ f '' I' = I)
    ⟨∅, M'.indep_empty, Set.image_empty f⟩
    (fun I J ⟨J', hJ', hfJ'⟩ _ => ⟨
      J' ∩ f ⁻¹' I,
      M'.indep_subset hJ' (by aesop),
      by rwa [Set.image_inter_preimage f J' I, hfJ', Set.inter_eq_right]
    ⟩)
    (by
      sorry
    )
    (by
      intro X hX I' ⟨I, hI, hfI⟩ hI'subset
      unfold Set.Nonempty maximals
      simp
      sorry
    )
    (fun I ⟨_, hI', hfI'⟩ => hfI' ▸ Set.image_subset f (M'.subset_ground _ hI'))
