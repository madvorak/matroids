import Mathlib.Data.Matroid.Restrict
import Matroids.Utilities.Sets


variable {α : Type*}

set_option linter.unusedVariables false in
/-- Direct sum of matroids as a set operation. -/
def indepDirectSum {M₁ M₂ : IndepMatroid α} (hME : M₁.E ∩ M₂.E = ∅) (I : Set α) : Prop :=
  ∃ I₁ I₂ : Set α, I₁ ∪ I₂ = I ∧ M₁.Indep I₁ ∧ M₂.Indep I₂
/-
A potential refactor which would be pretty lean but less compatible with `IndepMatroid` could be:
```
def indepDirectSum' (M₁ M₂ : IndepMatroid α) : Set (Set α) :=
  Set.image2 Set.union M₁.Indep M₂.Indep
```
-/

lemma indepDirectSum.ground {M₁ M₂ : IndepMatroid α} {I : Set α} {hME : M₁.E ∩ M₂.E = ∅}
    (hI : indepDirectSum hME I) :
    I ⊆ M₁.E ∪ M₂.E := by
  obtain ⟨_, _, rfl, hM₁, hM₂⟩ := hI
  exact Set.union_subset_union (M₁.subset_ground _ hM₁) (M₂.subset_ground _ hM₂)

def IndepMatroid.Indep.toLeft {M₁ M₂ : IndepMatroid α} {I : Set α} (hM₁ : M₁.Indep I) (hME : M₁.E ∩ M₂.E = ∅) :
    indepDirectSum hME I :=
  ⟨I, ∅, Set.union_empty I, hM₁, M₂.indep_empty⟩

def IndepMatroid.Indep.toRight {M₁ M₂ : IndepMatroid α} {I : Set α} (hM₂ : M₂.Indep I) (hME : M₁.E ∩ M₂.E = ∅) :
    indepDirectSum hME I :=
  ⟨∅, I, Set.empty_union I, M₁.indep_empty, hM₂⟩

lemma indepDirectSum.leftIndep {M₁ M₂ : IndepMatroid α} {hME : M₁.E ∩ M₂.E = ∅} {I : Set α}
    (hI : indepDirectSum hME I) :
    M₁.Indep (I ∩ M₁.E) := by
  obtain ⟨I₁, I₂, rfl, hI₁, hI₂⟩ := hI
  convert M₁.indep_subset hI₁ (Set.inter_subset_right M₁.E I₁) using 1
  exact Set.union_inter_supset_left_of_disjoint hME (M₂.subset_ground I₂ hI₂)

lemma indepDirectSum.rightIndep {M₁ M₂ : IndepMatroid α} {hME : M₁.E ∩ M₂.E = ∅} {I : Set α}
    (hI : indepDirectSum hME I) :
    M₂.Indep (I ∩ M₂.E) := by
  obtain ⟨I₁, I₂, rfl, hI₁, hI₂⟩ := hI
  convert M₂.indep_subset hI₂ (Set.inter_subset_right M₂.E I₂) using 1
  exact Set.union_inter_supset_right_of_disjoint hME (M₁.subset_ground I₁ hI₁)

lemma indepDirectSum_iff {M₁ M₂ : IndepMatroid α}
    (hME : M₁.E ∩ M₂.E = ∅) {I : Set α} (hI : I ⊆ M₁.E ∪ M₂.E) :
    indepDirectSum hME I ↔ M₁.Indep (I ∩ M₁.E) ∧ M₂.Indep (I ∩ M₂.E) :=
  ⟨fun hid => ⟨hid.leftIndep, hid.rightIndep⟩, fun ⟨hM₁, hM₂⟩ => ⟨I ∩ M₁.E, I ∩ M₂.E, by aesop⟩⟩

lemma indepDirectSum_maximals_iff {M₁ M₂ : IndepMatroid α} (hME : M₁.E ∩ M₂.E = ∅) (I : Set α) :
    I ∈ maximals (· ⊆ ·) {I | indepDirectSum hME I} ↔ -- TODO why does spelling `Set.Subset` break it?
    I ⊆ M₁.E ∪ M₂.E ∧ I ∩ M₁.E ∈ maximals (· ⊆ ·) M₁.Indep ∧ I ∩ M₂.E ∈ maximals (· ⊆ ·) M₂.Indep := by
  dsimp only [maximals, Set.mem_setOf_eq]
  constructor <;> intro hyp
  · have I_grounded : I ⊆ M₁.E ∪ M₂.E
    · exact hyp.left.ground
    rw [indepDirectSum_iff hME I_grounded] at hyp
    obtain ⟨⟨hM₁, hM₂⟩, hB⟩ := hyp
    have I_as : I = I ∩ M₁.E ∪ I ∩ M₂.E
    · exact Set.eq_union_inters_of_subset_union I_grounded
    constructor
    · exact I_grounded
    constructor
    · constructor
      · exact hM₁
      · intro B₁ hB₁ hI₁
        rw [I_as]
        specialize hB ⟨B₁, I ∩ M₂.E, rfl, hB₁, hM₂⟩ (by rw [I_as]; setauto)
        rw [Set.union_inter_distrib_right, Set.inter_assoc, Set.inter_assoc, Set.inter_comm M₂.E,
            hME, Set.inter_empty, Set.union_empty, Set.inter_self]
        exact Set.subset_inter_of_redundant_right hB (M₁.subset_ground _ hB₁)
    · constructor
      · exact hM₂
      · intro B₂ hB₂ hI₂
        rw [I_as]
        specialize hB ⟨I ∩ M₁.E, B₂, rfl, hM₁, hB₂⟩ (by rw [I_as]; setauto)
        rw [Set.union_inter_distrib_right, Set.inter_assoc, Set.inter_assoc,
            hME, Set.inter_empty, Set.empty_union, Set.inter_self]
        exact Set.subset_inter_of_redundant_left hB (M₂.subset_ground _ hB₂)
  · obtain ⟨I_grounded, ⟨hI₁, hB₁⟩, ⟨hI₂, hB₂⟩⟩ := hyp
    have I_as : I = I ∩ M₁.E ∪ I ∩ M₂.E
    · exact Set.eq_union_inters_of_subset_union I_grounded
    have I_indep : indepDirectSum hME I
    · exact ⟨_, _, I_as.symm, hI₁, hI₂⟩
    rw [indepDirectSum_iff hME I_indep.ground]
    constructor
    · exact ⟨hI₁, hI₂⟩
    · intro B hB hIB
      rw [Set.subset_iff_subsets_of_disjoint hB.ground]
      constructor
      · exact hB₁ hB.leftIndep (Set.inter_subset_inter_left M₁.E hIB)
      · exact hB₂ hB.rightIndep (Set.inter_subset_inter_left M₂.E hIB)

/-- Direct sum of matroids as a matroid defined by the independence axioms. -/
def indepMatroidDirectSum {M₁ M₂ : IndepMatroid α} (hME : M₁.E ∩ M₂.E = ∅) : IndepMatroid α :=
  IndepMatroid.mk
    (M₁.E ∪ M₂.E)
    (indepDirectSum hME)
    ⟨∅, ∅, Set.union_self ∅, M₁.indep_empty, M₂.indep_empty⟩
    (fun A B hMB hAB => by
      have hA : A ⊆ M₁.E ∪ M₂.E
      · exact hAB.trans hMB.ground
      rw [indepDirectSum_iff hME hA]
      rw [indepDirectSum_iff hME hMB.ground] at hMB
      rw [Set.subset_iff_subsets_of_disjoint hA] at hAB
      obtain ⟨hE₁, hE₂⟩ := hAB
      obtain ⟨hB₁, hB₂⟩ := hMB
      exact ⟨M₁.indep_subset hB₁ hE₁, M₂.indep_subset hB₂ hE₂⟩
    )
    (by
      intro I B hI I_not_max B_max

      -- split `B` into `B₁ = B ∩ M₁.E` and `B₂ = B ∩ M₂.E`
      rw [indepDirectSum_maximals_iff hME] at B_max
      obtain ⟨- , hB₁, hB₂⟩ := B_max

      -- split `I` into `I₁` and `I₂`
      have I_grounded := hI.ground
      rw [indepDirectSum_maximals_iff hME] at I_not_max
      rw [indepDirectSum_iff hME hI.ground] at hI
      simp only [I_grounded, not_true_eq_false, false_or, not_and_or] at I_not_max

      cases I_not_max with
      | inl hI₁ =>
        obtain ⟨x, hxBmI, M₁_aug⟩ := M₁.indep_aug hI.left hI₁ hB₁
        use x
        constructor
        · setesop
        rw [indepDirectSum_iff]
        constructor
        · convert M₁_aug using 1
          setesop
        convert hI.right using 1
        · setesop
        setesop
      | inr hI₂ =>
        obtain ⟨x, hxBmI, M₂_aug⟩ := M₂.indep_aug hI.right hI₂ hB₂
        use x
        constructor
        · setesop
        rw [indepDirectSum_iff]
        constructor
        swap
        · convert M₂_aug using 1
          setesop
        convert hI.left using 1
        · setesop
        setesop
    )
    (by
      intro X hX I hI hIX
      have I_grounded := hI.ground
      rw [indepDirectSum_iff hME I_grounded] at hI
      obtain ⟨hI₁, hI₂⟩ := hI

      -- define `S₁` and `S₂`
      obtain ⟨S₁, ⟨hMS₁, hIMS₁, hSE₁⟩, hS₁⟩ :=
        M₁.indep_maximal (X ∩ M₁.E) (Set.inter_subset_right X M₁.E) _ hI₁ (by
          rw [Set.subset_iff_subsets_of_disjoint I_grounded] at hIX
          exact hIX.left
        )
      obtain ⟨S₂, ⟨hMS₂, hIMS₂, hSE₂⟩, hS₂⟩ :=
        M₂.indep_maximal (X ∩ M₂.E) (Set.inter_subset_right X M₂.E) _ hI₂ (by
          rw [Set.subset_iff_subsets_of_disjoint I_grounded] at hIX
          exact hIX.right
        )

      -- apply `contr` to `S` → there is a strictly bigger set `T` with the same properties
      by_contra! contr
      unfold maximals at contr
      rw [Set.eq_empty_iff_forall_not_mem] at contr
      specialize contr (S₁ ∪ S₂)
      simp at contr
      obtain ⟨T, hTS₂, hTS₁, hTX, hIT, T_indep, T_big⟩ :=
        contr
          ⟨S₁, S₂, rfl, hMS₁, hMS₂⟩
          (by
            rw [Set.subset_iff_subsets_of_disjoint I_grounded]
            constructor
            · convert hIMS₁
              exact Set.union_inter_eq_fst hME hSE₁ hSE₂
            · convert hIMS₂
              exact Set.union_inter_eq_snd hME hSE₁ hSE₂
          )
          (Set.subset_inter_iff.mp hSE₁).left
          (Set.subset_inter_iff.mp hSE₂).left

      -- we will derive a contradiction with `T_big`
      apply T_big

      -- `S₁` and `S₂` contain parts of `T` by maximality
      have hT₁S₁ := hS₁ ⟨T_indep.leftIndep, Set.between_inter hIT hTX M₁.E⟩ (by
        convert Set.inter_subset_inter_left M₁.E hTS₁
        simp_all
      )
      have hT₂S₂ := hS₂ ⟨T_indep.rightIndep, Set.between_inter hIT hTX M₂.E⟩ (by
        convert Set.inter_subset_inter_left M₂.E hTS₂
        simp_all
      )
      convert Set.union_subset_union hT₁S₁ hT₂S₂
      rw [← Set.inter_union_distrib_left, Set.left_eq_inter]
      exact hTX.trans hX
    )
    (fun _ => (·.ground))

/-- Direct sum of matroids as a matroid defined by bases. -/
def matroidDirectSum {M₁ M₂ : Matroid α} (hME : M₁.E ∩ M₂.E = ∅) : Matroid α :=
  (indepMatroidDirectSum hME').matroid where
  hME' : (M₁.restrictIndepMatroid _).E ∩ (M₂.restrictIndepMatroid _).E = ∅ := hME

#print axioms indepMatroidDirectSum
