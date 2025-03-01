import MathlibExtraLean.FunctionUpdateITE


set_option autoImplicit false


def Function.updateFromListOfPairsITE
  {α β : Type}
  [DecidableEq α]
  (init : α → β) :
  List (α × β) → (α → β)
  | [] => init
  | hd :: tl => Function.updateITE (Function.updateFromListOfPairsITE init tl) hd.fst hd.snd


-------------------------------------------------------------------------------


def Function.updateFromListOfPairsITE_foldl
  {α β : Type}
  [DecidableEq α]
  (init : α → β)
  (l : List (α × β)) :
  α → β :=
  List.foldl (fun (prev : α → β) (next : α × β) => Function.updateITE prev next.fst next.snd) init l


def Function.updateFromListOfPairsITE_foldr
  {α β : Type}
  [DecidableEq α]
  (init : α → β)
  (l : List (α × β)) :
  α → β :=
  List.foldr (fun (next : α × β) (prev : α → β) => Function.updateITE prev next.fst next.snd) init l


#eval Function.updateFromListOfPairsITE (fun _ => 0) [(2, 8), (1, 2), (1, 5), (2, 3)] 3

#eval Function.updateFromListOfPairsITE_foldr (fun _ => 0) [(2, 8), (1, 2), (1, 5), (2, 3)] 3


example
  {α β : Type}
  [DecidableEq α]
  (init : α → β)
  (l : List (α × β)) :
  Function.updateFromListOfPairsITE init l = Function.updateFromListOfPairsITE_foldr init l :=
  by
  induction l
  case nil =>
    unfold Function.updateFromListOfPairsITE
    unfold Function.updateFromListOfPairsITE_foldr
    simp only [List.foldr_nil]
  case cons hd tl ih =>
    unfold Function.updateFromListOfPairsITE_foldr at ih

    unfold Function.updateFromListOfPairsITE
    unfold Function.updateFromListOfPairsITE_foldr
    simp only [List.foldr_cons]
    rewrite [ih]
    rfl


-------------------------------------------------------------------------------


example
  {α β : Type}
  [DecidableEq α]
  (init : α → β)
  (l : List (α × β))
  (x : α)
  (h1 : x ∉ l.map Prod.fst) :
  Function.updateFromListOfPairsITE init l x = init x :=
  by
  induction l
  case nil =>
    unfold Function.updateFromListOfPairsITE
    rfl
  case cons hd tl ih =>
    simp only [List.map_cons, List.mem_cons] at h1
    simp only [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold Function.updateFromListOfPairsITE
    unfold Function.updateITE
    split_ifs
    apply ih
    exact h1_right


example
  {α β : Type}
  [DecidableEq α]
  (init : α → β)
  (l : List (α × β))
  (a : α)
  (b : β)
  (h1 : (a, b) ∈ l)
  (h2 : ∀ (b' : β), (a, b') ∈ l → b' = b) :
  Function.updateFromListOfPairsITE init l a = b :=
  by
  induction l
  case nil =>
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    simp only [List.mem_cons] at h1

    simp only [List.mem_cons] at h2

    unfold Function.updateFromListOfPairsITE
    unfold Function.updateITE
    by_cases c1 : (a, b) = hd
    case pos =>
      split_ifs
      case pos c2 =>
        rewrite [← c1]
        simp only
      case neg c2 =>
        rewrite [← c1] at c2
        simp only at c2
        contradiction
    case neg =>
      split_ifs
      case pos c2 =>
        apply h2
        left
        rewrite [c2]
        simp only [Prod.mk.eta]
      case neg c2 =>
        apply ih
        · cases h1
          case inl h1_left =>
            contradiction
          case inr h1_right =>
            exact h1_right
        · intro b' a1
          apply h2
          right
          exact a1


-------------------------------------------------------------------------------


def Function.toListOfPairs
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (l : List α) :
  List (α × β) :=
  l.map (fun (x : α) => (x, f x))


lemma updateFromListOfPairsITE_of_toListOfPairs_not_mem
  {α β : Type}
  [DecidableEq α]
  (init : α → β)
  (f : α → β)
  (l : List α)
  (x : α)
  (h1 : x ∉ l) :
  Function.updateFromListOfPairsITE init (Function.toListOfPairs f l) x = init x :=
  by
  induction l
  case nil =>
    unfold Function.toListOfPairs
    simp only [List.map_nil]
    unfold Function.updateFromListOfPairsITE
    rfl
  case cons hd tl ih =>
    unfold Function.toListOfPairs at ih

    simp only [List.mem_cons] at h1
    simp only [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold Function.toListOfPairs
    simp only [List.map_cons]
    unfold Function.updateFromListOfPairsITE
    simp only
    unfold Function.updateITE
    split_ifs
    apply ih
    exact h1_right


lemma updateFromListOfPairsITE_of_toListOfPairs_mem
  {α β : Type}
  [DecidableEq α]
  (init : α → β)
  (f : α → β)
  (l : List α)
  (x : α)
  (h1 : x ∈ l) :
  Function.updateFromListOfPairsITE init (Function.toListOfPairs f l) x = f x :=
  by
  induction l
  case nil =>
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    unfold Function.toListOfPairs at ih

    simp only [List.mem_cons] at h1

    unfold Function.toListOfPairs
    simp only [List.map_cons]
    unfold Function.updateFromListOfPairsITE
    simp only
    unfold Function.updateITE
    split_ifs
    case pos c1 =>
      rewrite [c1]
      rfl
    case neg c1 =>
      apply ih
      cases h1
      case inl c2 =>
        contradiction
      case inr c2 =>
        exact c2


-------------------------------------------------------------------------------


lemma all_not_mem_are_init_imp_updateFromListOfPairsITE_of_toListOfPairs
  {α β : Type}
  [DecidableEq α]
  (init : α → β)
  (f : α → β)
  (l : List α)
  (h1 : ∀ x ∉ l, f x = init x) :
  (Function.updateFromListOfPairsITE init (Function.toListOfPairs f l)) = f :=
  by
  funext x
  by_cases c1 : x ∈ l
  case pos =>
    apply updateFromListOfPairsITE_of_toListOfPairs_mem
    exact c1
  case neg =>
    specialize h1 x c1
    rewrite [h1]
    apply updateFromListOfPairsITE_of_toListOfPairs_not_mem
    exact c1


lemma updateFromListOfPairsITE_of_toListOfPairs_imp_all_not_mem_are_init
  {α β : Type}
  [DecidableEq α]
  (init : α → β)
  (f : α → β)
  (l : List α)
  (h1 : (Function.updateFromListOfPairsITE init (Function.toListOfPairs f l)) = f) :
  ∀ x ∉ l, f x = init x :=
  by
  intro x a1
  rewrite [← h1]
  apply updateFromListOfPairsITE_of_toListOfPairs_not_mem
  exact a1
