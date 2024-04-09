import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Tactic.Have


def indepMatroidUnion {α : Type*} (M₁ M₂ : IndepMatroid α) (hME : M₁.E = M₂.E) :=
  IndepMatroid.mk
    M₁.E
    (fun I : Set α => ∃ I₁ I₂ : Set α, I₁ ∪ I₂ = I ∧ M₁.Indep I₁ ∧ M₂.Indep I₂)
    ⟨∅, ∅, Set.union_self ∅, M₁.indep_empty, M₂.indep_empty⟩
    (by
      intro I J ⟨J₁, J₂, hJ, hJ₁, hJ₂⟩ hIJ
      refine ⟨J₁ ∩ I, J₂ ∩ I, ?_,
        M₁.indep_subset hJ₁ (Set.inter_subset_left J₁ I),
        M₂.indep_subset hJ₂ (Set.inter_subset_left J₂ I)⟩
      apply Set.eq_of_subset_of_subset <;> intro x hx
      · cases hx with
        | inl hx₁ => exact hx₁.right
        | inr hx₂ => exact hx₂.right
      · have hxj : x ∈ J := hIJ hx
        rw [←hJ] at hxj
        rw [Set.mem_union] at hxj
        cases hxj with
        | inl hJ₁ => exact Or.inl ⟨hJ₁, hx⟩
        | inr hJ₂ => exact Or.inr ⟨hJ₂, hx⟩
    )
    (by
      intro I B ⟨I₁, I₂, hI, hI₁, hI₂⟩ hIni hBin
      rw [← hI] at hIni ⊢
      simp only at hIni hBin
      have hM₁ := M₁.indep_aug
      have hM₂ := M₂.indep_aug
      sorry
    )
    (by
      intro X hX
      simp [Matroid.ExistsMaximalSubsetProperty]
      intro A I₁ I₂ hA hI₁ hI₂ hAX
      obtain ⟨A₁, hM₁⟩ := M₁.indep_maximal X hX A sorry sorry
      obtain ⟨A₂, hM₂⟩ := M₂.indep_maximal X (hME ▸ hX) A sorry sorry
      use A₁ ∪ A₂
      constructor
      · sorry
      · intro B hB hAAB
        rw [Set.mem_setOf_eq] at hB
        obtain ⟨⟨C₁, C₂, hCB, hC₁, hC₂⟩, hAB, hBX⟩ := hB
        rw [←hCB] at *
        clear hCB
        sorry
    )
    (by
      intro I hI
      obtain ⟨_, _, rfl, hM₁, hM₂⟩ := hI
      exact Set.union_subset (M₁.subset_ground _ hM₁) (hME ▸ M₂.subset_ground _ hM₂)
    )
