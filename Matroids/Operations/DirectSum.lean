import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Tactic.Have
import Matroids.Automation.Tactics


variable {α : Type*}

lemma subset_iff_subsets_of_disjoint {A B E₁ E₂ : Set α} (hA : A ⊆ E₁ ∪ E₂) :
    A ⊆ B ↔ A ∩ E₁ ⊆ B ∩ E₁ ∧ A ∩ E₂ ⊆ B ∩ E₂ := by
  constructor
  · setauto
  · intro ⟨hE₁, hE₂⟩ x
    setauto
    specialize hA x
    specialize hE₁ x
    specialize hE₂ x
    tauto

lemma strict_subsets_of_disjoint {A B E₁ E₂ : Set α}
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

def indepDirectSum (M₁ M₂ : IndepMatroid α) (I : Set α) : Prop :=
  ∃ I₁ I₂ : Set α, I₁ ∪ I₂ = I ∧ M₁.Indep I₁ ∧ M₂.Indep I₂

/-
Potential refactor which would be pretty lean but less compatible with `IndepMatroid`:

def indepDirectSum (M₁ M₂ : IndepMatroid α) : Set (Set α) :=
  Set.image2 (· ∪ ·) M₁.Indep M₂.Indep
-/

lemma indepDirectSum_iff_of_disjoint {M₁ M₂ : IndepMatroid α}
    (hME : M₁.E ∩ M₂.E = ∅) {I : Set α} (hI : I ⊆ M₁.E ∪ M₂.E) :
    indepDirectSum M₁ M₂ I ↔ M₁.Indep (I ∩ M₁.E) ∧ M₂.Indep (I ∩ M₂.E) := by
  constructor
  · clear hI
    intro ⟨I₁, I₂, hI, hI₁, hI₂⟩
    rw [←hI]
    clear hI
    constructor
    · convert M₁.indep_subset hI₁ (Set.inter_subset_right M₁.E I₁) using 1
      rw [Set.union_inter_distrib_right]
      conv => rhs; rw [Set.inter_comm]
      convert Set.union_empty _
      have hM₂ := M₂.subset_ground I₂ hI₂
      setesop
    · convert M₂.indep_subset hI₂ (Set.inter_subset_right M₂.E I₂) using 1
      rw [Set.union_inter_distrib_right]
      conv => rhs; rw [Set.inter_comm]
      convert Set.empty_union _
      have hM₁ := M₁.subset_ground I₁ hI₁
      setesop
  · intro ⟨hM₁, hM₂⟩
    use I ∩ M₁.E, I ∩ M₂.E
    aesop

lemma indepDirectSum_ground {M₁ M₂ : IndepMatroid α} {I : Set α} (hI : indepDirectSum M₁ M₂ I) :
    I ⊆ M₁.E ∪ M₂.E := by
  obtain ⟨_, _, rfl, hM₁, hM₂⟩ := hI
  exact Set.union_subset_union (M₁.subset_ground _ hM₁) (M₂.subset_ground _ hM₂)

def indepMatroidDirectSum {M₁ M₂ : IndepMatroid α} (hME : M₁.E ∩ M₂.E = ∅) : IndepMatroid α :=
  IndepMatroid.mk
    (M₁.E ∪ M₂.E)
    (indepDirectSum M₁ M₂)
    ⟨∅, ∅, Set.union_self ∅, M₁.indep_empty, M₂.indep_empty⟩
    (fun A B hMB hAB => by
      have hA : A ⊆ M₁.E ∪ M₂.E
      · apply hAB.trans
        exact indepDirectSum_ground hMB
      rw [indepDirectSum_iff_of_disjoint hME hA]
      rw [indepDirectSum_iff_of_disjoint hME (indepDirectSum_ground hMB)] at hMB
      rw [subset_iff_subsets_of_disjoint hA] at hAB
      obtain ⟨hE₁, hE₂⟩ := hAB
      obtain ⟨hB₁, hB₂⟩ := hMB
      exact ⟨M₁.indep_subset hB₁ hE₁, M₂.indep_subset hB₂ hE₂⟩
    )
    (by
      intro I B ⟨I₁, I₂, hI, hI₁, hI₂⟩ hInimax hBinmax
      obtain ⟨⟨B₁, B₂, hB₁₂, hB₁, hB₂⟩, hBnoext⟩ := hBinmax
      rw [← hI] at *
      clear hI I
      if hI₁nimax: I₁ ∉ maximals Set.Subset M₁.Indep then
        sorry
      else if hI₂nimax: I₂ ∉ maximals Set.Subset M₂.Indep then
        sorry
      else
        exfalso
        simp [indepDirectSum, maximals] at hInimax hI₁nimax hI₂nimax
        obtain ⟨X, hXI₂, hXI₁, X₁, X₂, hMIX₂, hMIX₁, hX, hhX⟩ := hInimax I₁ I₂ rfl hI₁ hI₂
        apply hhX
        have hX₁ : I₁ ⊆ X₁ := by
          simp only [← hX] at *
          have hcap₁ : I₁ ∩ X₂ = ∅
          · clear * - hI₁ hMIX₁ hMIX₂ hME
            apply M₁.subset_ground at hMIX₁
            apply M₂.subset_ground at hMIX₂
            apply M₁.subset_ground at hI₁
            setesop
          clear * - hcap₁ hXI₁
          intro a ha
          cases hXI₁ ha with
          | inl haX₁ => exact haX₁
          | inr haX₂ =>
            exfalso
            have ha' : a ∈ I₁ ∩ X₂ := ⟨ha, haX₂⟩
            simp [hcap₁] at ha'
        have hX₂ : I₂ ⊆ X₂
        · simp only [← hX] at *
          have hcap₂ : I₂ ∩ X₁ = ∅
          · clear * - hI₂ hMIX₁ hMIX₂ hME
            apply M₁.subset_ground at hMIX₁
            apply M₂.subset_ground at hMIX₂
            apply M₂.subset_ground at hI₂
            setesop
          clear * - hcap₂ hXI₂
          intro a ha
          cases hXI₂ ha with
          | inl haX₁ =>
            exfalso
            have ha' : a ∈ I₂ ∩ X₁ := ⟨ha, haX₁⟩
            simp [hcap₂] at ha'
          | inr haX₂ => exact haX₂
        rw [← hX]
        sorry
    )
    (by
      intro X hX I ⟨I₁, I₂, hI₁₂, hI₁, hI₂⟩ hIX
      obtain ⟨T₁, hT₁⟩ := M₁.indep_maximal (X ∩ M₁.E) (Set.inter_subset_right X M₁.E) I₁ hI₁ sorry
      obtain ⟨T₂, hT₂⟩ := M₂.indep_maximal (X ∩ M₂.E) (Set.inter_subset_right X M₂.E) I₂ hI₂ sorry
      simp [maximals] at hT₁ hT₂ ⊢
      obtain ⟨⟨hindepT₁, hI₁subT₁, hT₁subX, hT₁subE⟩, hB₁⟩ := hT₁
      obtain ⟨⟨hindepT₂, hI₂subT₂, hT₂subX, hT₂subE⟩, hB₂⟩ := hT₂
      sorry
    )
    (fun _ => indepDirectSum_ground)
