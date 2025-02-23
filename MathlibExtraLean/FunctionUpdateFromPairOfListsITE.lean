import MathlibExtraLean.FunctionUpdateITE


set_option autoImplicit false


/--
  `Function.updateITE` at multiple points.
  `Function.updateFromPairOfListsITE f xs ys` := Replaces the value of `f` at each point in `xs` by the value in `ys` at the same index.
  If there are duplicate values in `xs` then the value at the smallest index is used.
  If the lengths of `xs` and `ys` do not match then the longer is effectively truncated to the length of the smaller.
-/
def Function.updateFromPairOfListsITE
  {α β : Type}
  [DecidableEq α]
  (f : α → β) :
  List α → List β → α → β
  | x :: xs, y :: ys => Function.updateITE (Function.updateFromPairOfListsITE f xs ys) x y
  | _, _ => f


#eval Function.updateFromPairOfListsITE (fun _ => 0) [5, 10, 5] [10, 20, 30] 5
#eval Function.updateFromPairOfListsITE (fun _ => 0) [5, 10, 5] [10, 20, 30] 10
#eval Function.updateFromPairOfListsITE (fun _ => 0) [5, 10, 5] [10, 20, 30] 15
#eval Function.updateFromPairOfListsITE (fun _ => 0) [5, 10] [10] 5
#eval Function.updateFromPairOfListsITE (fun _ => 0) [10] [5, 10] 10
#eval Function.updateFromPairOfListsITE (fun _ => 0) [] [5, 10] 10
#eval Function.updateFromPairOfListsITE (fun _ => 0) [5, 10] [] 5


theorem Function.updateFromPairOfListsITE_comp
  {α β γ : Type}
  [DecidableEq α]
  (f : α → β)
  (g : β → γ)
  (xs : List α)
  (ys : List β) :
  g ∘ Function.updateFromPairOfListsITE f xs ys =
    Function.updateFromPairOfListsITE (g ∘ f) xs (ys.map g) :=
  by
  induction xs generalizing ys
  case nil =>
    unfold Function.updateFromPairOfListsITE
    rfl
  case cons _ xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.map_nil]
      unfold Function.updateFromPairOfListsITE
      rfl
    case cons ys_hd ys_tl =>
      simp only [List.map_cons]
      unfold Function.updateFromPairOfListsITE
      rewrite [← xs_ih]
      apply Function.updateITE_comp_left


theorem Function.updateFromPairOfListsITE_mem'
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (xs ys : List α)
  (x : α)
  (h1 : f x = g x) :
  Function.updateFromPairOfListsITE f xs (List.map f ys) x =
    Function.updateFromPairOfListsITE g xs (List.map f ys) x :=
  by
  induction xs generalizing ys
  case nil =>
    unfold Function.updateFromPairOfListsITE
    exact h1
  case cons _ xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.map_nil]
      unfold Function.updateFromPairOfListsITE
      exact h1
    case cons ys_hd ys_tl =>
      simp only [List.map_cons]
      unfold Function.updateFromPairOfListsITE
      unfold Function.updateITE
      split_ifs
      · rfl
      · apply xs_ih


theorem Function.updateFromPairOfListsITE_mem_eq_len
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (v : α)
  (xs : List α)
  (ys : List β)
  (h1 : v ∈ xs)
  (h2 : xs.length = ys.length) :
  Function.updateFromPairOfListsITE f xs ys v =
    Function.updateFromPairOfListsITE g xs ys v :=
  by
  induction xs generalizing ys
  case nil =>
    simp only [List.not_mem_nil] at h1
  case cons xs_hd xs_tl xs_ih =>
    simp only [List.mem_cons] at h1

    cases ys
    case nil =>
      simp only [List.length_cons, List.length_nil] at h2
      contradiction
    case cons ys_hd ys_tl =>
      unfold Function.updateFromPairOfListsITE
      unfold Function.updateITE
      cases h1
      case inl h1 =>
        split_ifs
        rfl
      case inr h1 =>
        split_ifs
        case pos =>
          rfl
        case neg c1 =>
          simp only [List.length_cons] at h2
          simp only [Nat.succ.injEq] at h2
          apply xs_ih
          · exact h1
          · exact h2


theorem Function.updateFromPairOfListsITE_mem
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (v : α)
  (xs : List α)
  (ys : List β)
  (h1 : v ∈ xs)
  (h2 : f v = g v) :
  Function.updateFromPairOfListsITE f xs ys v =
    Function.updateFromPairOfListsITE g xs ys v :=
  by
  induction xs generalizing ys
  case nil =>
    contradiction
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.mem_cons] at h1

      unfold Function.updateFromPairOfListsITE
      exact h2
    case cons ys_hd ys_tl =>
      simp only [List.mem_cons] at h1

      unfold Function.updateFromPairOfListsITE
      unfold Function.updateITE
      split_ifs
      case pos =>
        rfl
      case neg c1 =>
        cases h1
        case inl c2 =>
          contradiction
        case inr c2 =>
          apply xs_ih
          exact c2


theorem Function.updateFromPairOfListsITE_not_mem
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (v : α)
  (xs : List α)
  (ys : List β)
  (h1 : v ∉ xs) :
  Function.updateFromPairOfListsITE f xs ys v = f v :=
  by
  induction xs generalizing ys
  case nil =>
    unfold Function.updateFromPairOfListsITE
    rfl
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      unfold Function.updateFromPairOfListsITE
      rfl
    case cons ys_hd ys_tl =>
      unfold Function.updateFromPairOfListsITE
      unfold Function.updateITE
      split_ifs
      case pos c1 =>
        rewrite [c1]
        simp only [List.mem_cons] at h1
        tauto
      case neg c1 =>
        simp only [List.mem_cons] at h1
        apply xs_ih
        tauto


theorem Function.updateFromPairOfListsITE_updateIte
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (xs : List α)
  (ys : List β)
  (x y : α)
  (z : β)
  (h1 : ¬ x = y) :
  Function.updateFromPairOfListsITE (Function.updateITE f y z) xs ys x =
    Function.updateFromPairOfListsITE f xs ys x :=
  by
  induction xs generalizing ys
  case nil =>
    unfold Function.updateFromPairOfListsITE
    unfold Function.updateITE
    split_ifs
    rfl
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      unfold Function.updateFromPairOfListsITE
      unfold Function.updateITE
      split_ifs
      rfl
    case cons ys_hd ys_tl =>
      unfold Function.updateFromPairOfListsITE
      unfold Function.updateITE
      split_ifs
      case pos c1 =>
        rfl
      case neg c1 =>
        apply xs_ih


theorem Function.updateFromPairOfListsITE_fun_coincide_mem_eq_len
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (xs ys : List α)
  (x : α)
  (h1 : ∀ (v : α), v ∈ ys → f v = g v)
  (h2 : x ∈ xs)
  (h3 : xs.length = ys.length) :
  Function.updateFromPairOfListsITE f xs (List.map f ys) x =
    Function.updateFromPairOfListsITE g xs (List.map g ys) x :=
  by
  have s1 : List.map f ys = List.map g ys
  simp only [List.map_eq_map_iff]
  exact h1

  rewrite [s1]
  apply Function.updateFromPairOfListsITE_mem_eq_len
  · exact h2
  · simp only [List.length_map]
    exact h3


theorem Function.updateFromPairOfListsITE_map_mem_ext
  {α β : Type}
  [DecidableEq α]
  (xs ys : List α)
  (f g h h' : α → β)
  (x : α)
  (h1 : ∀ (y : α), y ∈ ys → h y = h' y)
  (h2 : xs.length = ys.length)
  (h3 : x ∈ xs) :
  Function.updateFromPairOfListsITE f xs (List.map h ys) x =
      Function.updateFromPairOfListsITE g xs (List.map h' ys) x :=
  by
  have s1 : List.map h ys = List.map h' ys
  simp only [List.map_eq_map_iff]
  exact h1

  rewrite [s1]
  apply Function.updateFromPairOfListsITE_mem_eq_len
  · exact h3
  · simp only [List.length_map]
    exact h2


theorem Function.updateFromPairOfListsITE_map_mem
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (xs : List α)
  (x : α)
  (h1 : x ∈ xs) :
  Function.updateFromPairOfListsITE f xs (List.map g xs) x = g x :=
  by
  induction xs
  case nil =>
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    simp only [List.mem_cons] at h1

    simp only [List.map_cons]
    unfold Function.updateFromPairOfListsITE
    unfold Function.updateITE
    split_ifs
    case pos c1 =>
      rewrite [c1]
      rfl
    case neg c1 =>
      tauto


theorem Function.updateFromPairOfListsITE_map_updateIte
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (xs ys : List α)
  (v : α)
  (a : β)
  (x : α)
  (h1 : ∀ (y : α), y ∈ ys → ¬ y = v)
  (h2 : xs.length = ys.length)
  (h3 : x ∈ xs) :
  Function.updateFromPairOfListsITE f xs (List.map f ys) x =
  Function.updateFromPairOfListsITE g xs (List.map (Function.updateITE f v a) ys) x :=
  by
  apply updateFromPairOfListsITE_map_mem_ext
  · intro y a1
    unfold Function.updateITE
    split_ifs
    case pos c1 =>
      specialize h1 y a1
      contradiction
    case neg c2 =>
      rfl
  · exact h2
  · exact h3


#lint
