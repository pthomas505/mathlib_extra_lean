import MathlibExtraLean.FunctionUpdateITE


set_option autoImplicit false


/--
  Function.updateITE at multiple points.
  Function.updateFromPairOfListsITE f xs ys := Replaces the value of f at each point in xs by the value in ys at the same index.
  If there are duplicate values in xs then the value at the smallest index is used.
  If the lengths of xs and ys do not match then the longer is effectively truncated to the length of the smaller.
-/
def Function.updateFromPairOfListsITE
  {α β : Type}
  [DecidableEq α]
  (f : α → β) :
  List α → List β → α → β
  | x :: xs, y :: ys => Function.updateITE (Function.updateFromPairOfListsITE f xs ys) x y
  | _, _ => f

#eval Function.updateFromPairOfListsITE (fun (n : ℕ) => n) [5, 10, 5] [10, 20, 30] 5
#eval Function.updateFromPairOfListsITE (fun (n : ℕ) => n) [5, 10] [10] 5
#eval Function.updateFromPairOfListsITE (fun (n : ℕ) => n) [10] [5, 10] 10
#eval Function.updateFromPairOfListsITE (fun (n : ℕ) => n) [] [5, 10] 10
#eval Function.updateFromPairOfListsITE (fun (n : ℕ) => n) [5, 10] [] 5



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
    simp only [Function.updateFromPairOfListsITE]
  case cons _ xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp
      simp only [Function.updateFromPairOfListsITE]
    case cons ys_hd ys_tl =>
      simp
      simp only [Function.updateFromPairOfListsITE]
      simp only [← xs_ih]
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
    simp only [Function.updateFromPairOfListsITE]
    exact h1
  case cons _ xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp
      simp only [Function.updateFromPairOfListsITE]
      exact h1
    case cons ys_hd ys_tl =>
      simp
      simp only [Function.updateFromPairOfListsITE]
      simp only [Function.updateITE]
      split_ifs
      · rfl
      · exact xs_ih ys_tl


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
    contradiction
  case cons xs_hd xs_tl xs_ih =>
    simp at h1

    cases ys
    case nil =>
      contradiction
    case cons ys_hd ys_tl =>
      simp only [Function.updateFromPairOfListsITE]
      simp only [Function.updateITE]
      cases h1
      case inl h1 =>
        simp only [if_pos h1]
      case inr h1 =>
        split_ifs
        case pos =>
          rfl
        case neg c1 =>
          simp at h2
          exact xs_ih ys_tl h1 h2


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
      simp at h1

      simp only [Function.updateFromPairOfListsITE]
      exact h2
    case cons ys_hd ys_tl =>
      simp at h1

      simp only [Function.updateFromPairOfListsITE]
      simp only [Function.updateITE]
      split_ifs
      case pos =>
        rfl
      case neg c1 =>
        cases h1
        case inl c2 =>
          contradiction
        case inr c2 =>
          exact xs_ih ys_tl c2


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
    simp only [Function.updateFromPairOfListsITE]
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [Function.updateFromPairOfListsITE]
    case cons ys_hd ys_tl =>
      simp only [Function.updateFromPairOfListsITE]
      simp only [Function.updateITE]
      split_ifs
      case pos c1 =>
        subst c1
        simp at h1
      case neg c1 =>
        simp at h1
        push_neg at h1
        cases h1
        case intro h1_left h1_right =>
          apply xs_ih ys_tl h1_right


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
    simp only [Function.updateFromPairOfListsITE]
    simp only [Function.updateITE]
    simp only [if_neg h1]
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [Function.updateFromPairOfListsITE]
      simp only [Function.updateITE]
      simp only [if_neg h1]
    case cons ys_hd ys_tl =>
      simp only [Function.updateFromPairOfListsITE]
      simp only [Function.updateITE]
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
  (h3 : xs.length = ys.length):
  Function.updateFromPairOfListsITE f xs (List.map f ys) x =
    Function.updateFromPairOfListsITE g xs (List.map g ys) x :=
  by
  have s1 : List.map f ys = List.map g ys
  simp only [List.map_eq_map_iff]
  exact h1

  simp only [s1]
  apply Function.updateFromPairOfListsITE_mem_eq_len
  · exact h2
  · simp
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

  simp only [s1]
  apply Function.updateFromPairOfListsITE_mem_eq_len
  · exact h3
  · simp
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
    simp at h1
  case cons hd tl ih =>
    simp at h1

    simp
    simp only [Function.updateFromPairOfListsITE]
    simp only [Function.updateITE]
    split_ifs
    case _ c1 =>
      subst c1
      rfl
    case _ c1 =>
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
  have s1 : ∀ (y : α), y ∈ ys → f y =Function.updateITE f v a y
  intro y a1
  simp only [Function.updateITE]
  split_ifs
  case _ c1 =>
    specialize h1 y a1
    contradiction
  case _ c2 =>
    rfl

  exact Function.updateFromPairOfListsITE_map_mem_ext xs ys f g f (Function.updateITE f v a) x s1 h2 h3
