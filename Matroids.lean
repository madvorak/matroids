import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Data.Matrix.RowCol
import Mathlib.LinearAlgebra.LinearIndependent


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

def matroid_union {α : Type*} (M₁ M₂ : IndepMatroid α) (hME : M₁.E = M₂.E) :=
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
          --have := M₁.subset_ground I₁ hI₁
          --have := M₂.subset_ground X₂ hMIX₂
          have hX₁ : I₁ ⊆ X₁ := by
            simp only [← hX] at *
            have hcap₁ : I₁ ∩ X₂ = ∅ := sorry
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
            have hcap₂ : I₂ ∩ X₁ = ∅ := sorry
            clear * - hcap₂ hXI₂
            intro a ha
            cases hXI₂ ha with
            | inl h =>
              exfalso
              have : a ∈ I₂ ∩ X₁ := ⟨ha, h⟩
              simp [hcap₂] at this
            | inr h => exact h
          rw [← hX]
          intro a ha
          cases ha with
          | inl h =>
            left
            exact hI₁nimax.right X₁ hX₁ hMIX₁ h
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


example {F : Type} [Field F] {D E : Set F} (hDE : D ⊆ E)
    (hE : LinearIndependent F (Subtype.val : E → F)
      ) : LinearIndependent F (Subtype.val : D → F) :=
  LinearIndependent.mono hDE hE

example {F : Type} [Field F] {E : Set F}
    (hF : LinearIndependent F (Subtype.val : Set.univ.Elem → F)) :
    LinearIndependent F (Subtype.val : E → F) :=
  LinearIndependent.mono (fun _ _ => trivial) hF

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Linear.20independent.20equivalent.20formulations
example {ι F : Type} [Field F] {S : Set ι} {f : ι → F} :
    LinearIndependent F (f · : S → F) →
    LinearIndependent F (fun x => x : S.image f → F) := by
  sorry

def Matrix.indepMatroid {F m n : Type*} [Field F] [Fintype m] [Fintype n]
    (A : Matrix m n F) : IndepMatroid n :=
  IndepMatroid.mk
    Set.univ
    (fun S : Set n =>
      LinearIndependent F ((A.transpose ·) : S → (m → F)))
    (by convert linearIndependent_empty_type; aesop)
    (by
      intro I J indep subse
      have indep' : LinearIndependent F (fun x => x : J.image A.transpose → (m → F))
      · sorry
      suffices : LinearIndependent F (fun x => x : I.image A.transpose → (m → F))
      · sorry
      exact LinearIndependent.mono (Set.image_mono subse) indep'
    )
    sorry
    sorry
    sorry

def Matroid.IsVectorMatroid {F m n : Type*} [Field F] [Fintype m] [Fintype n]
    (M : Matroid n) : Prop :=
  ∃ A : Matrix m n F, A.indepMatroid.matroid = M
