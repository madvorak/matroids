import Mathlib.Data.Matroid.IndepAxioms

variable {α : Type*}

def IndepMatroid.Finite (M : IndepMatroid α) : Prop :=
  M.matroid.Finite

def IndepMatroid.ExistsMaximalSubsetProperty (P : Set α → Prop) (X : Set α) : Prop :=
  Matroid.ExistsMaximalSubsetProperty P X
