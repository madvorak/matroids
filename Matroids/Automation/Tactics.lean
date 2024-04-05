import Mathlib.Tactic.Tauto
import Mathlib.Data.Set.Basic

macro "setauto" : tactic =>
  `(tactic|
    simp only [Set.ext_iff, Set.mem_inter_iff, Set.mem_union, Set.not_mem_compl_iff] <;>
    tauto)

example (α : Type) (A B C : Set α) :
    (B ∪ C) ∩ A = (A ∩ C) ∪ (A ∩ B) := by
  setauto
