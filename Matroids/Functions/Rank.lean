import Mathlib.Data.ENat.Basic
import Mathlib.Order.SetNotation
import Matroids.IndepMatroid_aug
import Mathlib.Tactic.Have


variable {α : Type*}

/-- relative rank function -/
noncomputable def IndepMatroid.relativeRank (M : IndepMatroid α) {A B : Set α} (hA : A ⊆ M.E) (hB : B ⊆ A) : ℕ∞ :=
  ⨆ (J : {_J // _J ∈ maximals Set.Subset {X | M.Indep X ∧ X ⊆ B}}),
    ⨆ (I : {_I // M.Indep _I ∧ _I ⊆ A ∧ J.val ⊆ _I}),
      Set.encard (I.val \ J.val)

/-- relative rank of empty set and empty set is zero -/
lemma relativeRank_empty_empty {M : IndepMatroid α} :
    M.relativeRank (Set.empty_subset _) (Set.empty_subset _) = 0 := by
  sorry

/-- relative rank of two sets is at most cardinality of their difference -/
lemma relativeRank_le_encard {M : IndepMatroid α} {A B : Set α} (hA : A ⊆ M.E) (hB : B ⊆ A) :
    M.relativeRank hA hB ≤ Set.encard (A \ B) := by
  sorry

/-- relative rank with intersection in second argument is at least relative rank with union in first argument -/
lemma relativeRank_inter_ge_union {M : IndepMatroid α} {A B : Set α} (hA : A ⊆ M.E) (hB : B ⊆ M.E) :
    M.relativeRank hA (Set.inter_subset_left A B) ≥
    M.relativeRank (Set.union_subset hA hB) (Set.subset_union_right A B) := by
  sorry

/-- relative rank decomposes into a sum of relative ranks with an intermediate set -/
lemma relativeRank_telescope {M : IndepMatroid α} {A B C : Set α} (hA : A ⊆ M.E) (hB : B ⊆ A) (hC : C ⊆ B) :
    M.relativeRank hA (hC.trans hB) = M.relativeRank hA hB + M.relativeRank (hB.trans hA) hC := by
  sorry

/-- if relative rank is zero with set family in first argument, it is zero with union of that family -/
lemma relativeRank_family_zero {M : IndepMatroid α} {ι : Type} [Inhabited ι] {A : ι → Set α} {B : Set α}
    (hA : ∀ i : ι, A i ⊆ M.E) (hB : ∀ i : ι, B ⊆ A i) (hR : ∀ i : ι, M.relativeRank (hA i) (hB i) = 0) :
    M.relativeRank (Set.iUnion_subset hA) ((hB default).trans (Set.subset_iUnion_of_subset default (subset_refl _))) =
      0 := by
  sorry

/-- set of independent sets defined via relative rank function -/
def IndepMatroid.rankIndepSets (M : IndepMatroid α) : Set (Set α) :=
  { (I) | (I : Set α) (hI : I ⊆ M.E) (_ : ∀ x ∈ I, M.relativeRank hI (Set.diff_subset I {x}) > 0) }

/-- set of r-independent sets satisfies maximal property (extension to a maximal) -/
lemma rankIndepSets_have_maximals (M : IndepMatroid α) :
    -- todo: refactor using ExistsMaximalSubsetProperty?
    ∀ X ⊆ M.E, ∀ I : Set α, I ∈ M.rankIndepSets → I ⊆ X →
      Set.Nonempty (maximals Set.Subset {Y : Set α | Y ∈ M.rankIndepSets ∧ I ⊆ Y ∧ Y ⊆ X}) := by
  sorry

-- todo: equivalent definition of matroid via relative rank function --

/-- absolute rank function -/
noncomputable def IndepMatroid.absoluteRank (M : IndepMatroid α) {A : Set α} (hA : A ⊆ M.E) : ℕ∞ :=
  ⨆ (I : {_I // M.Indep _I ∧ _I ⊆ A}), Set.encard I.val

/-- correspondence between relative and absolute rank for finite matroids -/
lemma relativeRank_of_finite_eq_sub_absoluteRanks (M : IndepMatroid α) (hM : Set.Finite M.E)
    {A B : Set α} (hA : A ⊆ M.E) (hB : B ⊆ A) :
    M.relativeRank hA hB = M.absoluteRank hA - M.absoluteRank (hB.trans hA) := by
  sorry

/-- for finite matroids, absolute rank is integer between 0 and cardinality -/
lemma absoluteRank_of_finite_in_range (M : IndepMatroid α) (hM : Set.Finite M.E) {A : Set α} (hA : A ⊆ M.E) :
    ∃ r : ℕ, M.absoluteRank hA = some r ∧ 0 ≤ r ∧ r ≤ Set.ncard A := by
  sorry

/-- for finite matroids, absolute rank is monotone -/
lemma absoluteRank_of_finite_le (M : IndepMatroid α) (hM : Set.Finite M.E)
    {A B : Set α} (hA : A ⊆ M.E) (hB : B ⊆ A) :
    M.absoluteRank (hB.trans hA) ≤ M.absoluteRank hA := by
  sorry

/-- for finite matroids, absolute rank is submodular -/
lemma absoluteRank_of_finite_submodular (M : IndepMatroid α) (hM : Set.Finite M.E)
    {A B : Set α} (hA : A ⊆ M.E) (hB : B ⊆ M.E) :
    M.absoluteRank (Set.union_subset hA hB) + M.absoluteRank ((Set.inter_subset_left A B).trans hA) ≤
      M.absoluteRank hA + M.absoluteRank hB := by
  sorry

/-- for finite matroids, set is independent iff its rank equals its cardinality -/
lemma absoluteRank_of_finite_iff_indep (M : IndepMatroid α) (hM : Set.Finite M.E)
    {A : Set α} (hA : A ⊆ M.E) :
    M.Indep A ↔ M.absoluteRank hA = Set.encard A := by
  sorry

/-- for finite matroids, set is base iff its rank equals its cardinality and equals rank of matroid -/
lemma absoluteRank_of_finite_iff_base (M : IndepMatroid α) (hM : Set.Finite M.E)
    {A : Set α} (hA : A ⊆ M.E) :
    A ∈ maximals Set.Subset M.Indep ↔
      M.absoluteRank hA = Set.encard A ∧ M.absoluteRank hA = Set.encard M.E := by
  sorry
