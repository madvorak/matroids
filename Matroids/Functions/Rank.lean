import Mathlib.Data.ENat.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Matroid.IndepAxioms


-- definition of relative rank function
noncomputable def relativeRank {α : Type} (M : IndepMatroid α) {A B : Set α} (hA : A ⊆ M.E) (hB : B ⊆ A) : ℕ∞ :=
  ⨆ (J : {_J // _J ∈ maximals Set.Subset {X | M.Indep X ∧ X ⊆ B}}),
  ⨆ (I : {_I // M.Indep _I ∧ _I ⊆ A ∧ J.val ⊆ _I}),
  (Set.encard (I.val \ J.val))

-- relative rank of empty set and empty set is zero
lemma relativeRank_empty_empty {α : Type} (M : IndepMatroid α) :
    relativeRank M (Set.empty_subset _) (Set.empty_subset _) = 0 := by
  simp [relativeRank]

  -- rw [iSup_const]
  -- convert @iSup_const ENat _ _ (0 : ENat)

  -- swap
  -- convert iSup_const
  sorry

-- relative rank of two sets is at most cardinality of their difference
lemma relativeRank_le_encard {α : Type} (M : IndepMatroid α) {A B : Set α} (hA : A ⊆ M.E) (hB : B ⊆ A) :
    relativeRank M hA hB ≤ Set.encard (A \ B) := by
  sorry

-- relative rank with intersection in second argument is at least relative rank with union in first argument
lemma relativeRank_inter_ge_union {α : Type} (M : IndepMatroid α) {A B : Set α} (hA : A ⊆ M.E) (hB : B ⊆ M.E) :
    relativeRank M hA (Set.inter_subset_left A B)
    ≥ relativeRank M (Set.union_subset hA hB) (Set.subset_union_right A B) := by
  sorry

-- relative rank decomposes into a sum of relative ranks with an intermediate set
lemma relativeRank_telescope {α : Type} (M : IndepMatroid α) {A B C : Set α} (hA : A ⊆ M.E) (hB : B ⊆ A) (hC : C ⊆ B) :
    relativeRank M hA (hC.trans hB) = relativeRank M hA hB + relativeRank M (hB.trans hA) hC := by
  sorry

-- if relative rank is zero with set family in first argument, it is zero with union of that family
lemma relativeRank_family_zero {α : Type} (M : IndepMatroid α) {ι : Type} {{A : ι → Set α}} {B : Set α}
    (hA : ∀ i : ι, A i ⊆ M.E) (hB : ∀ i : ι, B ⊆ A i) (hR : ∀ i : ι, relativeRank M (hA i) (hB i) = 0) :
    relativeRank M (Set.iUnion_subset hA) (show B ⊆ Set.iUnion A by sorry) = 0
    := by
  sorry

-- todo: formulate lemma for the following statement
-- * (RM) consider collection all I ⊆ E s.t. r(I | I - x) > 0 ∀ x ∈ I. this collection satisfies (M)
--        (aka `indep_maximal`: if I ⊆ X ⊆ E and I ∈ collection, then {I' ∈ collection | I ⊆ I' ⊆ X} has a maximal element)

-- -- set of r-independent sets satisfies maximal property (extension to a maximal)
-- lemma relativeRank_indep_maximal {α : Type} (M : IndepMatroid α) :
--     := by
--   sorry

-- todo: formulate lemmas below

-- correspondence with finite rank: R(A) = r(A | ∅), r(A | B) = R(A) - R(B) for B ⊆ A
-- (R1-3) for relative rank convert to corresponding properties of finite rank

-- definition ("(finite) rank") for finite matroids: r(X) = max{|I| | I ⊆ X, I ∈ I(M)} = |maximal{I ∈ I(M) | I ⊆ X}|
-- properties for finite matroids:
-- * (R1) if X ⊆ E, then 0 ≤ r(X) ≤ |X|
-- * (R2) if X ⊆ Y ⊆ E, then r(X) ≤ r(Y)
-- * (R3, submodularity) if X, Y ⊆ E, then r(X ∪ Y) + r(X ∩ Y) ≤ r(X) + r(Y)
-- * if X, Y are such that r(X + y) = r(X) for all y ∈ Y, then r(X ∪ Y) = r(X)
-- * if r satisfies (R1-3), then (E, {X ⊆ E | r(X) = |X|}) is a matroid
-- * (cor) r is a rank function of a matroid iff r satisfies (R1-3)
-- def: r(M) = max{r(X) | X ⊆ E}
-- * X is indep iff r(X) = |X|
-- * X is a basis iff r(X) = |X| = r(M)
-- * X is a circuit iff X ≠ ∅ and ∀ x ∈ X, r(X - x) = |X| - 1 = r(X)
