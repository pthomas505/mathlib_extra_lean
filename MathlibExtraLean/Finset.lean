import MathlibExtraLean.FunctionUpdateITE


set_option linter.style.emptyLine false


theorem Finset.union_subset_left_right
  {α : Type}
  [DecidableEq α]
  (A B C D : Finset α)
  (h1 : A ⊆ C)
  (h2 : B ⊆ D) :
  A ∪ B ⊆ C ∪ D :=
  by
  apply Finset.union_subset_iff.mpr
  constructor
  · trans C
    · exact h1
    · exact Finset.subset_union_left
  · trans D
    · exact h2
    · exact Finset.subset_union_right


theorem Finset.union_subset_union_left_right
  {α : Type}
  [DecidableEq α]
  (A B C D E : Finset α)
  (h1 : A ⊆ C ∪ E)
  (h2 : B ⊆ D ∪ E) :
  A ∪ B ⊆ C ∪ D ∪ E :=
  by
  apply Finset.union_subset_iff.mpr
  constructor
  · trans C ∪ E
    · exact h1
    · apply Finset.union_subset_union_left
      exact Finset.subset_union_left
  · trans D ∪ E
    · exact h2
    · apply Finset.union_subset_union_left
      exact Finset.subset_union_right


theorem Finset.union_subset_diff
  {α : Type}
  [DecidableEq α]
  (A B C D E : Finset α)
  (h1 : A ⊆ C \ E)
  (h2 : B ⊆ D \ E) :
  A ∪ B ⊆ (C ∪ D) \ E :=
  by
  apply Finset.union_subset_iff.mpr
  constructor
  · trans C \ E
    · exact h1
    · apply Finset.sdiff_subset_sdiff
      · exact Finset.subset_union_left
      · apply Finset.Subset.refl
  · trans D \ E
    · exact h2
    · apply Finset.sdiff_subset_sdiff
      · exact Finset.subset_union_right
      · apply Finset.Subset.refl


theorem Finset.union_subset_left_right_diff
  {α : Type}
  [DecidableEq α]
  (A B C D E F : Finset α)
  (h1 : A ⊆ E ∪ C \ F)
  (h2 : B ⊆ E ∪ D \ F) :
  A ∪ B ⊆ E ∪ (C ∪ D) \ F :=
  by
  apply Finset.union_subset_iff.mpr
  constructor
  · trans E ∪ C \ F
    · exact h1
    · apply Finset.union_subset_union_right
      apply Finset.sdiff_subset_sdiff
      · exact Finset.subset_union_left
      · apply Finset.Subset.refl
  · trans E ∪ D \ F
    · exact h2
    · apply Finset.union_subset_union_right
      apply Finset.sdiff_subset_sdiff
      · exact Finset.subset_union_right
      · apply Finset.Subset.refl


theorem Finset.diff_union_subset
  {α : Type}
  [DecidableEq α]
  (A B C D E : Finset α)
  (h1 : A \ E ⊆ C)
  (h2 : B \ E ⊆ D) :
  (A ∪ B) \ E ⊆ C ∪ D :=
  by
  have s1 : (A ∪ B) \ E = (A \ E) ∪ (B \ E) :=
  by
    exact Finset.union_sdiff_distrib A B E

  trans (A \ E) ∪ (B \ E)
  · rewrite [s1]
    apply Finset.Subset.refl
  · apply Finset.union_subset_left_right
    · exact h1
    · exact h2


theorem Finset.union_right_comm_assoc
  {α : Type}
  [DecidableEq α]
  (x : α)
  (S T : Finset α) :
  (S ∪ (T ∪ {x})) = ((S ∪ {x}) ∪ T) :=
  by
  rewrite [Finset.union_right_comm S {x} T]
  rewrite [Finset.union_assoc S T {x}]
  apply Eq.refl


theorem Finset.image_sdiff_singleton
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (x : α)
  (x' : β)
  (f : α → β)
  (h1 : f x = x') :
  (Finset.image f S) \ {x'} =
  (Finset.image f (S \ {x})) \ {x'} :=
  by
  rewrite [← h1]
  ext a
  simp only [mem_sdiff, mem_image, mem_singleton]
  constructor
  · intro a1
    obtain ⟨⟨b, ⟨a1_left_left, a1_left_right⟩⟩, a1_right⟩ := a1
    constructor
    · apply Exists.intro b

      have s1 : ¬ b = x :=
      by
        intro contra
        apply a1_right
        rewrite [← contra]
        rewrite [← a1_left_right]
        apply Eq.refl

      constructor
      · constructor
        · exact a1_left_left
        · exact s1
      · exact a1_left_right
    · exact a1_right
  · intro a1
    obtain ⟨⟨b, ⟨⟨a1_left_left_left, a1_left_left_right⟩, a1_left_right⟩⟩, a1_right⟩ := a1
    constructor
    · apply Exists.intro b
      constructor
      · exact a1_left_left_left
      · exact a1_left_right
    · exact a1_right


theorem Finset.image_sdiff_singleton_updateITE
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (x : α)
  (x' : β)
  (f : α → β) :
  ((S \ {x}).image (Function.updateITE f x x')) =
  ((S \ {x}).image f) :=
  by
  apply Finset.image_congr
  simp only [Set.EqOn]
  intro a a1
  simp only [coe_sdiff, coe_singleton, Set.mem_sdiff, mem_coe, Set.mem_singleton_iff] at a1
  obtain ⟨a1_left, a1_right⟩ := a1
  simp only [Function.updateITE]
  split
  case isTrue c1 =>
    contradiction
  case isFalse c1 =>
    apply Eq.refl


theorem Finset.image_congr_update_ite
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (x : α)
  (a b : β)
  (f : α → β) :
  ((S \ {x}).image (Function.updateITE f x a)) =
  ((S \ {x}).image (Function.updateITE f x b)) :=
  by
  apply Finset.image_congr
  simp only [Set.EqOn]
  intro v a1
  simp only [coe_sdiff, coe_singleton, Set.mem_sdiff, mem_coe, Set.mem_singleton_iff] at a1
  obtain ⟨a1_left, a1_right⟩ := a1
  simp only [Function.updateITE]
  split
  case isTrue c1 =>
    contradiction
  case isFalse c1 =>
    apply Eq.refl


theorem Finset.mem_image_update
  {α : Type}
  [DecidableEq α]
  (x y : α)
  (f : α → α)
  (S : Finset α)
  (h1 : ¬ y = x)
  (h2 : y ∈ S) :
  f y ∈ Finset.image (Function.updateITE f x x) S :=
  by
  simp only [Finset.mem_image]
  apply Exists.intro y
  constructor
  · exact h2
  · simp only [Function.updateITE]
    split
    case isTrue c1 =>
      contradiction
    case isFalse c1 =>
      apply Eq.refl
