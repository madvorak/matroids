import Mathlib.Tactic.Tauto
import Mathlib.Data.Set.Basic


macro "setauto" : tactic =>
  `(tactic|
    try simp only [
      Set.ext_iff,
      Set.subset_def,
      Set.mem_inter_iff,
      Set.mem_union,
      Set.mem_compl_iff,
    ] at *
    <;>
    try tauto)

example (α : Type) (A : Set α) :
    A ⊆ Set.univ := by
  setauto

example (α : Type) (A : Set α) :
    ∅ ⊆ A := by
  setauto

example (α : Type) (A : Set α) (hA : A ⊆ ∅) :
    A = ∅ := by
  setauto

example (α : Type) (A : Set α) :
    Aᶜᶜ = A := by
  setauto

example (α : Type) (A B C : Set α) (hAB : A ⊆ B) (hBC : B ⊆ C) :
    A ⊆ C := by
  setauto

example (α : Type) (A : Set α) (hA : Aᶜ ⊆ ∅) :
    A = Set.univ := by
  setauto
  intro x
  specialize hA x
  tauto

example (α : Type) (A B C : Set α) :
    (B ∪ C) ∩ A = (A ∩ C) ∪ (A ∩ B) := by
  setauto

example (α : Type) (A B C : Set α) :
    (Aᶜ ∪ B ∪ C)ᶜ = Cᶜ ∩ Bᶜ ∩ A := by
  setauto

example (α : Type) (A B C : Set α) :
    (Aᶜ ∩ B ∩ Cᶜᶜ)ᶜᶜᶜᶜᶜ = Cᶜ ∪ Bᶜ ∪ ∅ ∪ A ∪ ∅ := by
  setauto

example (α : Type) (A B C D : Set α) :
    D ∩ (B ∪ Cᶜ) ∩ A = (Aᶜᶜ ∩ Cᶜᶜᶜ ∩ D) ∪ (A ∩ Dᶜᶜ ∩ B)ᶜᶜ := by
  setauto


macro "setesop" : tactic =>
  `(tactic|
    try simp only [
      Set.ext_iff,
      Set.subset_def,
      Set.mem_inter_iff,
      Set.mem_union,
      Set.mem_compl_iff,
    ] at *
    <;>
    try aesop)
