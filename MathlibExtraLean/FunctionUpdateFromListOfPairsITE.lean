import MathlibExtraLean.FunctionUpdateITE


set_option autoImplicit false


def Function.updateFromListOfPairsITE
  {α β : Type}
  [DecidableEq α]
  (f : α → β) :
  List (α × β) → (α → β)
  | [] => f
  | hd :: tl => Function.updateITE (Function.updateFromListOfPairsITE f tl) hd.fst hd.snd


def Function.updateFromListOfPairsITE_foldl
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (l : List (α × β)) :
  α → β :=
  List.foldl (fun (prev : α → β) (next : α × β) => Function.updateITE prev next.fst next.snd) f l


def Function.updateFromListOfPairsITE_foldr
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (l : List (α × β)) :
  α → β :=
  List.foldr (fun (next : α × β) (prev : α → β) => Function.updateITE prev next.fst next.snd) f l


#eval Function.updateFromListOfPairsITE (fun _ => 0) [(2, 8), (1, 2), (1, 5), (2, 3)] 3

#eval Function.updateFromListOfPairsITE_foldr (fun _ => 0) [(2, 8), (1, 2), (1, 5), (2, 3)] 3


example
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (l : List (α × β)) :
  Function.updateFromListOfPairsITE f l = Function.updateFromListOfPairsITE_foldr f l :=
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
