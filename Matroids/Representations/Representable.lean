import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Tactic.Have


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
      · sorry -- Wrong! Does not suffice!
      exact LinearIndependent.mono (Set.image_mono subse) indep'
    )
    sorry
    sorry
    sorry

def Matroid.IsVectorMatroid {F m n : Type*} [Field F] [Fintype m] [Fintype n]
    (M : Matroid n) : Prop :=
  ∃ A : Matrix m n F, A.indepMatroid.matroid = M
