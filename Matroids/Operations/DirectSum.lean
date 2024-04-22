import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Tactic.Have
import Matroids.Automation.Tactics


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

lemma Set.chain_to_components {E₁ E₂ I T X : Set α} (hME : E₁ ∩ E₂ = ∅)
     (hIT : I ⊆ T) (hTX : T ⊆ X) (hX : X ⊆ E₁ ∪ E₂) :
    ((I ∩ E₁) ⊆ (T ∩ E₁) ∧ (T ∩ E₁) ⊆ (X ∩ E₁)) ∧
    ((I ∩ E₂) ⊆ (T ∩ E₂) ∧ (T ∩ E₂) ⊆ (X ∩ E₂)) := by
  setauto


def indepDirectSum (M₁ M₂ : IndepMatroid α) (I : Set α) : Prop :=
  ∃ I₁ I₂ : Set α, I₁ ∪ I₂ = I ∧ M₁.Indep I₁ ∧ M₂.Indep I₂

def indepDirectSum_left {M₁ M₂ : IndepMatroid α} {I : Set α} (hM₁ : M₁.Indep I) :
    indepDirectSum M₁ M₂ I :=
  ⟨I, ∅, Set.union_empty I, hM₁, M₂.indep_empty⟩

def indepDirectSum_right {M₁ M₂ : IndepMatroid α} {I : Set α} (hM₂ : M₂.Indep I) :
    indepDirectSum M₁ M₂ I :=
  ⟨∅, I, Set.empty_union I, M₁.indep_empty, hM₂⟩

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

lemma indepDirectSum_iff_disjoint_maximals {M₁ M₂ : IndepMatroid α} (hME : M₁.E ∩ M₂.E = ∅) {I : Set α} :
    I ∈ maximals (· ⊆ ·) {I | indepDirectSum M₁ M₂ I} ↔
      I ∩ M₁.E ∈ maximals (· ⊆ ·) M₁.Indep ∧ I ∩ M₂.E ∈ maximals (· ⊆ ·) M₂.Indep := by
  dsimp only [maximals, Set.mem_setOf_eq]
  constructor <;> intro hyp
  · rw [indepDirectSum_iff_of_disjoint hME sorry] at hyp
    obtain ⟨⟨hM₁, hM₂⟩, hb⟩ := hyp
    have I_as : I = I ∩ M₁.E ∪ I ∩ M₂.E
    · apply Set.eq_union_inters_of_disjoint
      apply indepDirectSum_ground
      sorry
    constructor
    · constructor
      · exact hM₁
      · intro B₁ hB₁ hI₁
        rw [I_as]
        specialize hb ⟨B₁, I ∩ M₂.E, rfl, hB₁, hM₂⟩ (by rw [I_as]; setauto)
        rw [Set.union_inter_distrib_right, Set.inter_assoc, Set.inter_assoc, Set.inter_comm M₂.E,
            hME, Set.inter_empty, Set.union_empty, Set.inter_self]
        exact Set.subset_inter_of_redundant_right hb (M₁.subset_ground _ hB₁)
    · constructor
      · exact hM₂
      · intro B₂ hB₂ hI₂
        rw [I_as]
        specialize hb ⟨I ∩ M₁.E, B₂, rfl, hM₁, hB₂⟩ (by rw [I_as]; setauto)
        rw [Set.union_inter_distrib_right, Set.inter_assoc, Set.inter_assoc,
            hME, Set.inter_empty, Set.empty_union, Set.inter_self]
        exact Set.subset_inter_of_redundant_left hb (M₂.subset_ground _ hB₂)
  -- = >
  -- by contradiction: assume one component is not maximal
  -- then we can expand it while preserving independence
  -- drag it to disjoint union, contradicts maximality
  -- repeat for both components
  -- <=
  -- by contradiction: suppose not maximal in union
  -- then we can expand it
  -- extra element is in `M₁` or `M₂`
  -- drag it to components, contradicts maximality
  · rw [indepDirectSum_iff_of_disjoint hME (indepDirectSum_ground _)]
    obtain ⟨hyp₁, hyp₂⟩ := hyp
    have I_as : I = I ∩ M₁.E ∪ I ∩ M₂.E
    · apply Set.eq_union_inters_of_disjoint
      apply indepDirectSum_ground
      sorry
    constructor
    · tauto
    · intro B hB hIB
      have hM₁ : M₁.Indep (B ∩ M₁.E)
      · sorry
      have hM₂ : M₂.Indep (B ∩ M₂.E)
      · sorry
      have hB₁ := hyp₁.right hM₁ (by setauto)
      have hB₂ := hyp₂.right hM₂ (by setauto)
      rw [I_as] at *
      setauto
      intro x hx
      specialize hME x
      specialize hB₁ x
      specialize hB₂ x
      specialize hIB x
      sorry
    · sorry

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
      rw [Set.subset_iff_subsets_of_disjoint hA] at hAB
      obtain ⟨hE₁, hE₂⟩ := hAB
      obtain ⟨hB₁, hB₂⟩ := hMB
      exact ⟨M₁.indep_subset hB₁ hE₁, M₂.indep_subset hB₂ hE₂⟩
    )
    (by
      intro I B hI hInotmax hBmax

      -- split `B` into `B₁ = B ∩ M₁.E` and `B₂`
      rw [indepDirectSum_iff_disjoint_maximals hME] at hBmax
      obtain ⟨hB₁, hB₂⟩ := hBmax

      -- split `I` into `I₁` and `I₂`
      rw [indepDirectSum_iff_disjoint_maximals hME, not_and_or] at hInotmax

      have hhI := hI
      rw [indepDirectSum_iff_of_disjoint hME (indepDirectSum_ground hI)] at hI

      cases hInotmax with
      | inl hI₁ =>
          obtain ⟨x, hxBmI, hxAug⟩ := M₁.indep_aug hI.left hI₁ hB₁
          use x
          constructor
          · setesop
          rw [indepDirectSum_iff_of_disjoint]
          constructor
          · convert hxAug using 1
            setesop
          convert hI.right using 1
          · setesop
          · exact hME
          rw [Set.insert_subset_iff, Set.mem_union]
          constructor
          · setesop
          · exact indepDirectSum_ground hhI
      | inr hI₂ =>
          obtain ⟨x, hxBmI, hxAug⟩ := M₂.indep_aug hI.right hI₂ hB₂
          use x
          constructor
          · setesop
          rw [indepDirectSum_iff_of_disjoint]
          constructor
          swap
          · convert hxAug using 1
            setesop
          convert hI.left using 1
          · setesop
          · exact hME
          rw [Set.insert_subset_iff, Set.mem_union]
          constructor
          · setesop
          · exact indepDirectSum_ground hhI
    )
    (by
      intro X hX I hI hIX
      have hIinground := indepDirectSum_ground hI
      rw [indepDirectSum_iff_of_disjoint hME hIinground] at hI
      obtain ⟨hI₁, hI₂⟩ := hI

      -- define `S₁` and `S₂`
      obtain ⟨S₁, hS₁⟩ := M₁.indep_maximal (X ∩ M₁.E) (Set.inter_subset_right X M₁.E) _ hI₁ (by
        rw [Set.subset_iff_subsets_of_disjoint hIinground] at hIX
        exact hIX.left
      )
      obtain ⟨S₂, hS₂⟩ := M₂.indep_maximal (X ∩ M₂.E) (Set.inter_subset_right X M₂.E) _ hI₂ (by
        rw [Set.subset_iff_subsets_of_disjoint hIinground] at hIX
        exact hIX.right
      )
      dsimp [maximals] at hS₁ hS₂

      -- apply `contr` to `S` → there is a strictly bigger `S'` with the same properties
      by_contra! contr
      unfold maximals at contr
      rw [Set.eq_empty_iff_forall_not_mem] at contr
      specialize contr (S₁ ∪ S₂)
      simp at contr
      obtain ⟨T, hTS₂, hTS₁, hTX, hIT, hTindep, hTbig⟩ :=
        contr sorry sorry sorry sorry  -- by `hS₁`, `hS₂`, and some set theory

      -- we will derive a contradiction with `hTbig`
      apply hTbig

      have hTE₁ : M₁.Indep (T ∩ M₁.E)
      · sorry
      have hTE₂ : M₂.Indep (T ∩ M₂.E)
      · sorry
      -- split `T` into parts
      obtain ⟨hT₁, hT₂⟩ := Set.chain_to_components hME hIT hTX hX

      -- `S₁` and `S₂` contain parts of `T` by maximality
      have hT₁S₁ := hS₁.right ⟨hTE₁, hT₁⟩ (by  -- set theory
        have hTS₁' : S₁ ∩ M₁.E ⊆ T ∩ M₁.E
        · apply Set.inter_subset_inter hTS₁
          rfl
        convert hTS₁'
        -- follows from `hTS₁`, `hT₁₂`, and `hS₁.left.right.right`
        sorry
      )
      have hT₂S₂ := hS₂.right ⟨hTE₂, hT₂⟩ (by -- set theory, similar to above
        sorry
      )

      -- clean up
      convert Set.union_subset_union hT₁S₁ hT₂S₂
      rw [← Set.inter_union_distrib_left, Set.left_eq_inter]
      exact hTX.trans hX
    )
    (fun _ => indepDirectSum_ground)
