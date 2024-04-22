
theorem forall_and_forall {α : Type} (P Q : α → Prop) [Inhabited α] (hPQ : ∀ a b, P a ∧ Q b) :
    (∀ a, P a) ∧ (∀ b, Q b) :=
  ⟨fun n => (hPQ n default).left, fun m => (hPQ default m).right⟩
