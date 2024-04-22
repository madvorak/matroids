
theorem forall_forall_and_iff {α β : Type} (P : α → Prop) (Q : β → Prop) [Inhabited α] [Inhabited β] :
    (∀ a b, P a ∧ Q b) ↔ (∀ a, P a) ∧ (∀ b, Q b) :=
  ⟨fun hpq => ⟨fun a : α => (hpq a default).left, fun b : β => (hpq default b).right⟩,
  fun ⟨hp, hq⟩ => fun a : α => fun b : β => ⟨hp a, hq b⟩⟩
