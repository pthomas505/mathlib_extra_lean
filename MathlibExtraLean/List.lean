import MathlibExtraLean.FunctionUpdateITE


set_option autoImplicit false


lemma List.map_eq_self_imp_fun_is_id_on_mem
  {α : Type}
  (f : α → α)
  (xs : List α)
  (h1 : xs.map f = xs) :
  ∀ (x : α), x ∈ xs → f x = x :=
  by
  intro x a1
  induction xs
  case nil =>
    simp only [not_mem_nil] at a1
  case cons hd tl ih =>
    simp only [map_cons, cons.injEq] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [mem_cons] at a1
    cases a1
    case inl a1_left =>
      rewrite [a1_left]
      exact h1_left
    case inr a1_right =>
      apply ih
      · exact h1_right
      · exact a1_right


lemma List.fun_is_id_on_mem_imp_map_eq_self
  {α : Type}
  (f : α → α)
  (xs: List α)
  (h1: ∀ (x : α), x ∈ xs → f x = x) :
  xs.map f = xs :=
  by
  induction xs
  case nil =>
    simp only [map_nil]
  case cons hd tl ih =>
    simp only [mem_cons] at h1

    simp only [map_cons, cons.injEq]
    constructor
    · apply h1
      left
      rfl
    · apply ih
      intro x a1
      apply h1
      right
      exact a1


theorem List.map_eq_self_iff_fun_is_id_on_mem
  {α : Type}
  (f : α → α)
  (xs : List α) :
  xs.map f = xs ↔
    ∀ (x : α), x ∈ xs → f x = x :=
  by
  constructor
  · apply List.map_eq_self_imp_fun_is_id_on_mem
  · apply List.fun_is_id_on_mem_imp_map_eq_self


example
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (f g : α → β)
  (a b : α)
  (h1 : Function.Injective f)
  (h2_left : g a = f b)
  (h2_right : g b = f a)
  (h3 : ∀ (x : α), (¬ x = a ∧ ¬ x = b) → f x = g x) :
  Function.Injective g :=
  by
  unfold Function.Injective at h1

  unfold Function.Injective
  intro x1 x2 a1
  by_cases x1_a : x1 = a
  · by_cases x2_a : x2 = a
    · rewrite [x1_a]
      rewrite [x2_a]
      rfl
    · by_cases x1_b : x1 = b
      · by_cases x2_b : x2 = b
        · rewrite [x1_b]
          rewrite [x2_b]
          rfl
        · have s1 : f x2 = g x2 :=
          by
            apply h3
            exact ⟨x2_a, x2_b⟩

          apply h1
          rewrite [x1_a]
          rewrite [← h2_right]
          rewrite [← x1_b]
          rewrite [a1]
          rewrite [← s1]
          rfl
      · by_cases x2_b : x2 = b
        · apply h1
          rewrite [x1_a]
          rewrite [x2_b]
          rewrite [x1_a] at a1
          rewrite [x2_b] at a1
          rewrite [← h2_left]
          rewrite [a1]
          rewrite [← h2_right]
          rfl
        · have s1 : f x2 = g x2 :=
          by
            apply h3
            exact ⟨x2_a, x2_b⟩

          exfalso
          apply x2_b
          apply h1
          rewrite [← h2_left]
          rewrite [← x1_a]
          rewrite [a1]
          exact s1
  · by_cases x2_a : x2 = a
    · by_cases x1_b : x1 = b
      · apply h1
        rewrite [x1_b]
        rewrite [← h2_left]
        rewrite [← x2_a]
        rewrite [← a1]
        rewrite [x1_b]
        rewrite [x2_a]
        exact h2_right
      · by_cases x2_b : x2 = b
        · have s1 : f x1 = g x1 :=
          by
            apply h3
            exact ⟨x1_a, x1_b⟩

          apply h1
          rewrite [x2_a]
          rewrite [← h2_right]
          rewrite [← x2_b]
          rewrite [← a1]
          exact s1
        · have s1 : f x1 = g x1 :=
          by
            apply h3
            exact ⟨x1_a, x1_b⟩

          exfalso
          apply x1_b
          apply h1
          rewrite [← h2_left]
          rewrite [← x2_a]
          rewrite [← a1]
          exact s1
    · by_cases x1_b : x1 = b
      · by_cases x2_b : x2 = b
        · rewrite [x1_b]
          rewrite [x2_b]
          rfl
        · have s1 : f x2 = g x2 :=
          by
            apply h3
            exact ⟨x2_a, x2_b⟩

          exfalso
          apply x2_a
          apply h1
          rewrite [← h2_right]
          rewrite [← x1_b]
          rewrite [a1]
          exact s1
      · by_cases x2_b : x2 = b
        · have s1 : f x1 = g x1 :=
          by
            apply h3
            exact ⟨x1_a, x1_b⟩

          exfalso
          apply x1_a
          apply h1
          rewrite [← h2_right]
          rewrite [← x2_b]
          rewrite [← a1]
          exact s1
        · have s1 : f x1 = g x1 :=
          by
            apply h3
            exact ⟨x1_a, x1_b⟩

          have s2 : f x2 = g x2 :=
          by
            apply h3
            exact ⟨x2_a, x2_b⟩

          apply h1
          rewrite [s1]
          rewrite [s2]
          exact a1


/--
  List.InjOn f xs := f is injective on xs if the restriction of f to xs is injective.
-/
def List.InjOn
  {α : Type}
  (f : α → α)
  (xs : List α) :
  Prop := ∀ ⦃x₁ : α⦄, x₁ ∈ xs → ∀ ⦃x₂ : α⦄, x₂ ∈ xs → f x₁ = f x₂ → x₁ = x₂


lemma List.nodup_eq_len_imp_exists_bijon
  {α : Type}
  [DecidableEq α]
  (xs ys : List α)
  (h1 : xs.length = ys.length)
  (h2 : xs.Nodup)
  (h3 : ys.Nodup) :
  ∃ (f : α → α), List.InjOn f xs ∧ xs.map f = ys :=
  by
  induction xs generalizing ys
  case nil =>
    apply Exists.intro id
    constructor
    · unfold InjOn
      intro x1 a1 x2 a2 a3
      unfold id at a3
      exact a3
    · have s1 : ys = [] :=
      by
        apply List.eq_nil_of_length_eq_zero
        rewrite [← h1]
        simp only [length_nil]

      rewrite [s1]
      simp only [map_nil]
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [length_cons, length_nil] at h1
      contradiction
    case cons ys_hd ys_tl =>
      simp only [length_cons] at h1
      simp only [Nat.succ.injEq] at h1

      simp only [nodup_cons] at h2
      obtain ⟨h2_left, h2_right⟩ := h2

      simp only [nodup_cons] at h3
      obtain ⟨h3_left, h3_right⟩ := h3

      obtain ⟨f, ⟨a1_left, a1_right⟩⟩ := xs_ih ys_tl h1 h2_right h3_right

      apply Exists.intro (Function.updateITE f xs_hd ys_hd)
      constructor
      · unfold List.InjOn
        intro x1 x1_mem x2 x2_mem
        simp only [mem_cons] at x1_mem
        simp only [mem_cons] at x2_mem

        unfold Function.updateITE
        split_ifs
        case pos c1 c2 =>
          intro _
          rewrite [c1]
          rewrite [c2]
          rfl
        case _ c1 c2 =>
          intro a2
          cases x2_mem
          case inl c3 =>
            contradiction
          case inr c3 =>
            obtain s1 := List.mem_map_of_mem c3
            rewrite [a1_right] at s1
            rewrite [← a2] at s1
            contradiction
        case _ c1 c2 =>
          intro a2
          cases x1_mem
          case inl c3 =>
            contradiction
          case inr c3 =>
            obtain s1 := List.mem_map_of_mem c3
            rewrite [a1_right] at s1
            rewrite [a2] at s1
            contradiction
        case _ c1 c2 =>
          intro a2
          cases x1_mem
          case inl x1_mem_left =>
            contradiction
          case inr x1_mem_right =>
            cases x2_mem
            case inl x2_mem_left =>
              contradiction
            case inr x2_mem_right =>
              unfold List.InjOn at a1_left
              exact a1_left x1_mem_right x2_mem_right a2
      · simp only [map_cons, cons.injEq]
        constructor
        · unfold Function.updateITE
          split_ifs
          case pos c1 =>
            rfl
          case neg c1 =>
            contradiction
        · rewrite [← a1_right]
          apply Function.updateITE_not_mem_list
          exact h2_left


theorem nodup_eq_len_imp_eqv
  {α : Type}
  [DecidableEq α]
  (xs ys : List α)
  (h1 : xs.length = ys.length)
  (h2 : xs.Nodup)
  (h3 : ys.Nodup) :
  ∃ (f : α ≃ α), xs.map f = ys :=
  by sorry


-------------------------------------------------------------------------------


lemma List.foldr_cons_append_init
  {α β : Type}
  (f : α → β)
  (xs_left xs_right : List β)
  (ys : List α) :
  List.foldr (fun (next : α) (prev : List β) => (f next) :: prev) (xs_left ++ xs_right) ys =
    (List.foldr (fun (next : α) (prev : List β) => (f next) :: prev) xs_left ys) ++ xs_right :=
  by
  induction ys
  case nil =>
    simp only [List.foldr_nil]
  case cons hd tl ih =>
    simp only [List.foldr_cons, List.cons_append]
    rewrite [ih]
    rfl


lemma List.length_eq_and_mem_zip_imp_fun_eq_imp_map_eq
  {α β γ : Type}
  (f : α → γ)
  (g : β → γ)
  (xs : List α)
  (ys : List β)
  (h1 : xs.length = ys.length)
  (h2 : ∀ (p : α × β), p ∈ List.zip xs ys → f p.fst = g p.snd) :
  List.map f xs = List.map g ys :=
  by
  induction xs generalizing ys f g
  case nil =>
    cases ys
    case nil =>
      simp only [List.map_nil]
    case cons ys_hd ys_tl =>
      simp only [List.length_nil, List.length_cons] at h1
      simp only [Nat.zero_ne_add_one] at h1
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.length_cons, List.length_nil] at h1
      simp only [Nat.add_one_ne_zero] at h1
    case cons ys_hd ys_tl =>
      simp only [List.length_cons, add_left_inj] at h1

      simp only [List.zip_cons_cons, List.mem_cons] at h2

      simp only [List.map_cons, List.cons.injEq]
      constructor
      · specialize h2 (xs_hd, ys_hd)
        apply h2
        left
        rfl
      · apply xs_ih
        · exact h1
        · intro p a1
          apply h2
          right
          exact a1


lemma List.mem_zip_filter_and_pred_eq_all_mem_zip_imp_mem_zip
  {α : Type}
  (xs ys : List α)
  (pred : α → Bool)
  (p : α × α)
  (h1 : p ∈ List.zip (List.filter pred xs) (List.filter pred ys))
  (h2 : ∀ (q : α × α), q ∈ List.zip xs ys → pred q.1 = pred q.2) :
  p ∈ List.zip xs ys :=
  by
  induction xs generalizing ys
  case nil =>
    simp only [List.filter_nil, List.zip_nil_left, List.not_mem_nil] at h1
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.filter_nil, List.zip_nil_right, List.not_mem_nil] at h1
    case cons ys_hd ys_tl =>
      simp only [List.filter_cons] at h1

      simp only [List.zip_cons_cons, List.mem_cons] at h2

      simp only [List.zip_cons_cons, List.mem_cons]
      split_ifs at h1
      case pos c1 c2 =>
        simp only [List.zip_cons_cons, List.mem_cons] at h1
        cases h1
        case inl h1 =>
          left
          exact h1
        case inr h1 =>
          right
          apply xs_ih
          · exact h1
          · intro q a1
            apply h2
            right
            exact a1
      case neg c1 c2 =>
        exfalso
        apply c2
        rewrite [← c1]
        specialize h2 (xs_hd, ys_hd)
        simp only at h2
        rewrite [← h2]
        · rfl
        · left
          exact trivial
      case pos c1 c2 =>
        exfalso
        apply c1
        rewrite [← c2]
        specialize h2 (xs_hd, ys_hd)
        simp only at h2
        apply h2
        left
        exact trivial
      case neg c1 c2 =>
        right
        apply xs_ih
        · exact h1
        · intro q a1
          apply h2
          right
          exact a1


lemma List.pred_eq_all_mem_zip_imp_filter_length_eq
  {α : Type}
  (xs ys : List α)
  (pred : α → Bool)
  (h1 : xs.length = ys.length)
  (h2 : ∀ (p : α × α), p ∈ List.zip xs ys → pred p.1 = pred p.2) :
  (List.filter pred xs).length = (List.filter pred ys).length :=
  by
  induction xs generalizing ys
  case nil =>
    cases ys
    case nil =>
      simp only [List.filter_nil, List.length_nil]
    case cons ys_hd ys_tl =>
      simp only [List.length_nil, List.length_cons] at h1
      simp only [Nat.zero_ne_add_one] at h1
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.length_cons, List.length_nil] at h1
      simp only [Nat.add_one_ne_zero] at h1
    case cons ys_hd ys_tl =>
      simp only [List.length_cons, add_left_inj] at h1

      simp only [List.zip_cons_cons, List.mem_cons] at h2

      simp only [List.filter_cons]
      split_ifs
      case pos c1 c2 =>
        simp only [List.length_cons, add_left_inj]
        apply xs_ih
        · exact h1
        · intro p a1
          apply h2
          right
          exact a1
      case neg c1 c2 =>
        exfalso
        apply c2
        rewrite [← c1]
        specialize h2 (xs_hd, ys_hd)
        simp only at h2
        rewrite [← h2]
        · rfl
        · left
          exact trivial
      case pos c1 c2 =>
        exfalso
        apply c1
        rewrite [← c2]
        specialize h2 (xs_hd, ys_hd)
        simp only at h2
        apply h2
        left
        exact trivial
      case neg c1 c2 =>
        apply xs_ih
        · exact h1
        · intro p a1
          apply h2
          right
          exact a1


lemma List.map_union
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (f : α → β)
  (l1 l2 : List α)
  (h1 : Function.Injective f) :
  List.map f (l1 ∪ l2) = (List.map f l1) ∪ (List.map f l2) :=
  by
  induction l1
  case nil =>
    simp only [List.map_nil]
    simp only [List.nil_union]
  case cons hd tl ih =>
    simp only [List.cons_union, List.map_cons]
    rewrite [← ih]
    unfold List.insert

    have s1 : List.elem (f hd) (List.map f (tl ∪ l2)) = true ↔ List.elem hd (tl ∪ l2) = true :=
    by
      simp only [List.elem_eq_mem, decide_eq_true_eq]
      apply List.mem_map_of_injective
      exact h1

    simp only [s1]
    split_ifs
    case pos c1 =>
      rfl
    case neg c1 =>
      simp only [List.map_cons]


-------------------------------------------------------------------------------


lemma List.exists_maximal_subset
  {α : Type}
  [DecidableEq α]
  (ll : List (List α))
  (h1 : ¬ ll = []) :
  ∃ (xs : List α), xs ∈ ll ∧
    ∀ (ys : List α), (ys ∈ ll ∧ xs ⊆ ys) → ys ⊆ xs :=
  by
  induction ll
  case nil =>
    contradiction
  case cons hd tl ih =>
    by_cases c1 : tl = []
    case pos =>
      rewrite [c1]
      apply Exists.intro hd
      constructor
      · simp only [List.mem_singleton]
      · intro ys a1
        obtain ⟨a1_left, a1_right⟩ := a1
        simp only [List.mem_singleton] at a1_left
        rewrite [a1_left]
        apply List.Subset.refl
    case neg =>
      specialize ih c1
      obtain ⟨xs, ih_left, ih_right⟩ := ih

      by_cases c2 : xs ⊆ hd
      case pos =>
        simp only [List.mem_cons]
        apply Exists.intro hd
        constructor
        · left
          rfl
        · intro ys a1
          obtain ⟨a1_left, a1_right⟩ := a1
          cases a1_left
          case inl a1_left =>
            rewrite [a1_left]
            apply List.Subset.refl
          case inr a1_left =>
            trans xs
            · apply ih_right
              constructor
              · exact a1_left
              · trans hd
                · exact c2
                · exact a1_right
            · exact c2
      case neg =>
        simp only [List.mem_cons]
        apply Exists.intro xs
        constructor
        · right
          exact ih_left
        · intro ys a1
          obtain ⟨a1_left, a1_right⟩ := a1
          cases a1_left
          case inl a1_left =>
            rewrite [a1_left] at a1_right
            contradiction
          case inr a1_left =>
            apply ih_right
            exact ⟨a1_left, a1_right⟩


lemma List.exists_minimal_subset
  {α : Type}
  [DecidableEq α]
  (ll : List (List α))
  (h1 : ¬ ll = []) :
  ∃ (xs : List α), xs ∈ ll ∧
    ∀ (ys : List α), (ys ∈ ll ∧ ys ⊆ xs) → xs ⊆ ys :=
  by
  induction ll
  case nil =>
    contradiction
  case cons hd tl ih =>
    by_cases c1 : tl = []
    case pos =>
      rewrite [c1]
      apply Exists.intro hd
      constructor
      · simp only [mem_singleton]
      · intro ys a1
        obtain ⟨a1_left, a1_right⟩ := a1
        simp only [mem_singleton] at a1_left
        rewrite [a1_left]
        apply List.Subset.refl
    case neg =>
      specialize ih c1
      obtain ⟨xs, ih_left, ih_right⟩ := ih

      by_cases c2 : hd ⊆ xs
      case pos =>
        simp only [List.mem_cons]
        apply Exists.intro hd
        constructor
        · left
          rfl
        · intro ys a1
          obtain ⟨a1_left, a1_right⟩ := a1
          cases a1_left
          case inl a1_left =>
            rewrite [a1_left]
            apply List.Subset.refl
          case inr a1_left =>
            trans xs
            · exact c2
            · apply ih_right
              constructor
              · exact a1_left
              · trans hd
                · exact a1_right
                · exact c2
      case neg =>
        simp only [List.mem_cons]
        apply Exists.intro xs
        constructor
        · right
          exact ih_left
        · intro ys a1
          obtain ⟨a1_left, a1_right⟩ := a1
          cases a1_left
          case inl a1_left =>
            rewrite [a1_left] at a1_right
            contradiction
          case inr a1_left =>
            apply ih_right
            exact ⟨a1_left, a1_right⟩


lemma List.exists_minimal_subset_of_mem
  {α : Type}
  [DecidableEq α]
  (ll : List (List α))
  (l : List α)
  (h1 : l ∈ ll) :
  ∃ (xs : List α), xs ∈ ll ∧ xs ⊆ l ∧
    ∀ (ys : List α), (ys ∈ ll ∧ ys ⊆ xs) → xs ⊆ ys :=
  by
  let ll' : List (List α) := List.filter (fun (l' : List α) => l' ⊆ l) ll

  have s1 : l ∈ ll' :=
  by
    simp only [ll']
    simp only [List.mem_filter]
    simp only [decide_eq_true_iff]
    constructor
    · exact h1
    · apply List.Subset.refl

  have s2 : ¬ ll' = [] :=
  by
    intro contra
    rewrite [contra] at s1
    simp only [List.not_mem_nil] at s1

  obtain ⟨xs, s1_left, s1_right⟩ := List.exists_minimal_subset ll' s2

  simp only [ll'] at s1_left
  simp only [List.mem_filter] at s1_left
  simp only [decide_eq_true_iff] at s1_left
  obtain ⟨s1_left_left, s1_left_right⟩ := s1_left

  apply Exists.intro xs
  constructor
  · exact s1_left_left
  · constructor
    · exact s1_left_right
    · intro ys a1
      obtain ⟨a1_left, a1_right⟩ := a1
      apply s1_right
      constructor
      · simp only [ll']
        simp only [List.mem_filter]
        simp only [decide_eq_true_iff]
        constructor
        · exact a1_left
        · trans xs
          · exact a1_right
          · exact s1_left_right
      · exact a1_right


-------------------------------------------------------------------------------


example
  {α : Type}
  (l : List α)
  (h1 : ¬ l = []) :
  ∃ (xs zs : List α) (y : α), l = xs ++ [y] ++ zs :=
  by
  induction l
  case nil =>
    contradiction
  case cons hd tl ih =>
    by_cases c1 : tl = []
    · rewrite [c1]
      apply Exists.intro []
      apply Exists.intro []
      apply Exists.intro hd
      simp only [List.nil_append, List.singleton_append]
    · obtain ⟨xs, zs, y, eq⟩ := ih c1
      apply Exists.intro (hd :: xs)
      apply Exists.intro zs
      apply Exists.intro y
      rewrite [eq]
      simp only [List.append_assoc, List.singleton_append, List.cons_append]


lemma List.exists_mem_imp_exists_leftmost_mem
  {α : Type}
  (l : List α)
  (f : α → Prop)
  (h1 : ∃ (x : α), x ∈ l ∧ f x) :
  ∃ (ll : List α) (y : α) (rl : List α),
    l = ll ++ [y] ++ rl ∧
    f y ∧
    ∀ (a : α), a ∈ ll → ¬ f a :=
  by
  induction l
  case nil =>
    obtain ⟨x, ⟨h1_left, h1_right⟩⟩ := h1
    simp only [not_mem_nil] at h1_left
  case cons hd tl ih =>
    simp only [append_assoc, singleton_append] at ih

    obtain ⟨x, ⟨h1_left, h1_right⟩⟩ := h1
    simp only [mem_cons] at h1_left

    simp only [append_assoc, singleton_append]
    by_cases c1 : f hd
    case pos =>
      apply Exists.intro []
      simp only [nil_append, cons.injEq]
      apply Exists.intro hd
      apply Exists.intro tl
      constructor
      · constructor
        · rfl
        · rfl
      · constructor
        · exact c1
        · intro a a1
          simp only [not_mem_nil] at a1
    case neg =>
      cases h1_left
      case inl h1_left_left =>
        rewrite [h1_left_left] at h1_right
        contradiction
      case inr h1_left_right =>
        have s1 : ∃ x ∈ tl, f x :=
        by
          apply Exists.intro x
          exact ⟨h1_left_right, h1_right⟩
        specialize ih s1

        obtain ⟨ll, y, rl, a1, a2, a3⟩ := ih

        apply Exists.intro (hd :: ll)
        apply Exists.intro y
        apply Exists.intro rl
        constructor
        · rewrite [a1]
          simp only [cons_append]
        · constructor
          · exact a2
          · intro a a4
            simp only [mem_cons] at a4
            cases a4
            case inl h4_left =>
              rewrite [h4_left]
              exact c1
            case inr h4_right =>
              apply a3
              exact h4_right


lemma List.exists_mem_imp_exists_rightmost_mem
  {α : Type}
  (l : List α)
  (f : α → Prop)
  (h1 : ∃ (x : α), x ∈ l ∧ f x) :
  ∃ (ll : List α) (y : α) (rl : List α),
    l = ll ++ [y] ++ rl ∧
    f y ∧
    ∀ (a : α), a ∈ rl → ¬ f a :=
  by
  induction l
  case nil =>
    obtain ⟨x, ⟨h1_left, h1_right⟩⟩ := h1
    simp only [not_mem_nil] at h1_left
  case cons hd tl ih =>
    simp only [append_assoc, singleton_append] at ih

    simp only [mem_cons] at h1
    obtain ⟨x, ⟨h1_left, h1_right⟩⟩ := h1

    simp only [append_assoc, singleton_append]
    by_cases c1 : ∃ x ∈ tl, f x
    case pos =>
      specialize ih c1
      obtain ⟨ll, y, rl, a1, a2, a3⟩ := ih
      apply Exists.intro (hd :: ll)
      apply Exists.intro y
      apply Exists.intro rl
      constructor
      · rewrite [a1]
        simp only [cons_append]
      · exact ⟨a2, a3⟩
    case neg =>
      cases h1_left
      case inl h1_left_left =>
        apply Exists.intro []
        apply Exists.intro hd
        apply Exists.intro tl
        constructor
        · simp only [nil_append]
        · constructor
          · rewrite [← h1_left_left]
            exact h1_right
          · intro a a1 contra
            apply c1
            apply Exists.intro a
            exact ⟨a1, contra⟩
      case inr h1_left_right =>
        exfalso
        apply c1
        apply Exists.intro x
        exact ⟨h1_left_right, h1_right⟩


-------------------------------------------------------------------------------

/-
protected def append : (xs ys : List α) → List α
  | [],    bs => bs
  | a::as, bs => a :: List.append as bs
-/


lemma List.length_nil_
  {α : Type} :
  ([] : List α).length = 0 :=
  by
  unfold List.length
  rfl


lemma List.length_cons_
  {α : Type}
  (a : α)
  (as : List α) :
  (a :: as).length = as.length + 1 :=
  by
  induction as generalizing a
  case nil =>
    unfold List.length
    rewrite [List.length_nil_]
    rfl
  case cons hd tl ih =>
    unfold List.length
    specialize ih hd
    rewrite [ih]
    rfl


lemma List.nil_append_
  {α : Type}
  (as : List α) :
  [] ++ as = as :=
  by
  unfold_projs
  unfold List.append
  rfl


lemma List.cons_append_
  {α : Type}
  (a : α)
  (as bs : List α) :
  (a :: as) ++ bs = a :: (as ++ bs) :=
  by
  unfold_projs
  conv =>
    lhs
    unfold List.append


lemma List.append_nil_
  {α : Type}
  (as : List α) :
  as ++ [] = as :=
  by
  induction as
  case nil =>
    unfold_projs
    unfold List.append
    rfl
  case cons hd tl ih =>
    rewrite [List.cons_append_]
    rewrite [ih]
    rfl


lemma List.length_append_
  {α : Type}
  (as bs : List α) :
  (as ++ bs).length = as.length + bs.length :=
  by
  induction as
  case nil =>
    rewrite [List.nil_append_]
    rewrite [List.length_nil_]
    rewrite [Nat.add_comm]
    unfold_projs
    unfold Nat.add
    rfl
  case cons hd tl ih =>
    simp only [cons_append_, length_cons_]
    rewrite [ih]
    exact Nat.add_right_comm tl.length bs.length 1


-------------------------------------------------------------------------------

-- https://github.com/mn200/CFL-HOL/blob/06c070d2d1775a933a1b667a29b035fee6a59796/lib/listLemmasScript.sml


example
  {α : Type}
  (l1 l2 l3 : List α) :
  (l1 ++ l2 = l1 ++ l3) ↔ (l2 = l3) :=
  by
  exact List.append_right_inj l1


lemma lreseq
  (α : Type)
  (l1 l2 : List α)
  (x y : α) :
  l1 ++ [x] ++ l2 = [y] ↔ x = y ∧ l1 = [] ∧ l2 = [] :=
  by
  constructor
  · intro a1
    cases l1
    case nil =>
      simp only [List.nil_append, List.singleton_append, List.cons.injEq] at a1
      obtain ⟨a1_left, a1_right⟩ := a1
      constructor
      · exact a1_left
      · constructor
        · rfl
        · exact a1_right
    case cons hd tl =>
      simp only [List.cons_append, List.append_assoc, List.singleton_append, List.cons.injEq, List.append_eq_nil, List.nil_append] at a1
      obtain ⟨a1_left, ⟨a1_right_left, a1_right_right⟩⟩ := a1
      contradiction
  · simp only [List.append_assoc, List.singleton_append]
    intro a1
    obtain ⟨a1_left, ⟨a1_right_left, a1_right_right⟩⟩ := a1
    rewrite [a1_right_left]
    rewrite [a1_right_right]
    simp only [List.nil_append]
    rewrite [a1_left]
    rfl


lemma rgr_r9
  {α : Type}
  (r : List α)
  (sym : α)
  (h1 : sym ∈ r) :
  ∃ r1 r2, r = r1 ++ [sym] ++ r2 :=
  by
  induction r
  case nil =>
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    simp only [List.mem_cons] at h1
    cases h1
    case inl h1_left =>
      rewrite [h1_left]
      apply Exists.intro []
      apply Exists.intro tl
      simp only [List.nil_append, List.singleton_append]
    case inr h1_right =>
      specialize ih h1_right
      obtain ⟨r1, r2, a1⟩ := ih
      apply Exists.intro (hd :: r1)
      apply Exists.intro r2
      rewrite [a1]
      simp only [List.append_assoc, List.singleton_append, List.cons_append]


lemma rgr_r9b
  {α : Type}
  (r : List α)
  (sym : α)
  (h1 : ∃ (r1 r2 : List α), r = r1 ++ [sym] ++ r2) :
  sym ∈ r :=
  by
  obtain ⟨r1, r2, eq⟩ := h1
  rewrite [eq]
  simp only [List.append_assoc, List.singleton_append, List.mem_append, List.mem_cons]
  right
  left
  exact trivial


lemma rgr_r9eq
  {α : Type}
  (r : List α)
  (sym : α) :
  sym ∈ r ↔ (∃ r1 r2, r = r1 ++ [sym] ++ r2) :=
  by
  constructor
  · intro a1
    exact rgr_r9 r sym a1
  · intro a1
    exact rgr_r9b r sym a1


lemma list_r1
  {α : Type}
  (v v' : List α)
  (x : α)
  (h1 : v = v' ++ [x]) :
  x ∈ v :=
  by
  rewrite [h1]
  simp only [List.mem_append, List.mem_singleton]
  right
  exact trivial


lemma append_eq_singleton
  {α : Type}
  (l1 l2 : List α)
  (e : α) :
  (l1 ++ l2 = [e]) ↔ (l1 = [e]) ∧ (l2 = []) ∨ (l1 = []) ∧ (l2 = [e]) :=
  by
  cases l1
  case nil =>
    simp only [List.nil_append]
    tauto
  case cons hd tl =>
    simp only [List.cons_append, List.cons.injEq, List.append_eq_nil]
    tauto


lemma list_r2
  {α : Type}
  (sl_1 sl_2 rhs : List α)
  (x : α)
  (h1 : sl_1 ++ rhs ++ sl_2 = [x])
  (h2 : ¬ rhs = []) :
  sl_1 = [] ∧ sl_2 = [] :=
  by
  simp only [append_eq_singleton] at h1
  cases h1
  case inl h1_left =>
    tauto
  case inr h1_right =>
    obtain ⟨h1_right_left, h1_right_right⟩ := h1_right
    simp only [List.append_eq_nil] at h1_right_left
    obtain ⟨h1_right_left_left, h1_right_right_right⟩ := h1_right_left
    contradiction


#lint
