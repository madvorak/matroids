import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.IndepAxioms


def IndepMatroid.Finite {α : Type} (M : IndepMatroid α) : Prop :=
  M.matroid.Finite


def IndepMatroid.ExistsMaximalSubsetProperty {α : Type _} (P : Set α → Prop) (X : Set α) : Prop :=
  Matroid.ExistsMaximalSubsetProperty P X
