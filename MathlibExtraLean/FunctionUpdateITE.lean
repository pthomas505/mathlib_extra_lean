import Mathlib.Tactic


set_option autoImplicit false


/--
  Specialized version of Function.update for non-dependent functions.
  Function.updateITE f a b := Replaces the value of f at a by b.
-/
def Function.updateITE
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a : α)
  (b : β)
  (c : α) :
  β :=
  if c = a then b else f c

#eval Function.updateITE (fun (n : ℕ) => n) 5 10 1
#eval Function.updateITE (fun (n : ℕ) => n) 5 10 5


/--
  Symmetric equality version of Function.updateITE.
-/
def Function.updateITE'
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a : α)
  (b : β)
  (c : α) :
  β :=
  if a = c then b else f c


/--
  Function.updateITE at multiple points.
  Function.updateListITE f xs ys := Replaces the value of f at each point in xs by the value in ys at the same index.
  If there are duplicate values in xs then the value at the smallest index is used.
  If the lengths of xs and ys do not match then the longer is effectively truncated to the length of the smaller.
-/
def Function.updateListITE
  {α β : Type}
  [DecidableEq α]
  (f : α → β) :
  List α → List β → α → β
  | x :: xs, y :: ys => Function.updateITE (Function.updateListITE f xs ys) x y
  | _, _ => f

#eval Function.updateListITE (fun (n : ℕ) => n) [5, 10, 5] [10, 20, 30] 5
#eval Function.updateListITE (fun (n : ℕ) => n) [5, 10] [10] 5
#eval Function.updateListITE (fun (n : ℕ) => n) [10] [5, 10] 10
#eval Function.updateListITE (fun (n : ℕ) => n) [] [5, 10] 10
#eval Function.updateListITE (fun (n : ℕ) => n) [5, 10] [] 5


/-
def Function.updateListITE'
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (xs : List α)
  (ys : List β) :
  α → β :=
  List.foldr (fun (p : α × β) (_ : α → β) => Function.updateITE f p.fst p.snd) f (List.zip xs ys)

#eval Function.updateListITE' (fun (n : ℕ) => n) [0, 3, 0] [10, 2, 2] 0
-/


lemma Function.left_id_left_inverse
  {α β : Type}
  (f : α → β)
  (g : β → α)
  (h1 : g ∘ f = id) :
  Function.LeftInverse g f :=
  by
  simp only [Function.LeftInverse]
  intro x
  exact congrFun h1 x


lemma Function.right_id_right_inverse
  {α β : Type}
  (f : α → β)
  (g : β → α)
  (h1 : f ∘ g = id) :
  Function.RightInverse g f :=
  by
  simp only [Function.RightInverse]
  exact Function.left_id_left_inverse g f h1


-- Function.updateITE

lemma Function.updateITE_eq_Function.updateITE'
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a : α)
  (b : β) :
  Function.updateITE f a b =
    Function.updateITE' f a b :=
  by
  funext x
  simp only [Function.updateITE]
  simp only [Function.updateITE']
  split_ifs
  case _ c1 c2 =>
    rfl
  case _ c1 c2 =>
    subst c1
    contradiction
  case _ c1 c2 =>
    subst c2
    contradiction
  case _ c1 c2 =>
    rfl


theorem Function.updateITE_comp_left
  {α β γ : Type}
  [DecidableEq α]
  (f : β → γ)
  (g : α → β)
  (a : α)
  (b : β) :
  f ∘ (Function.updateITE g a b) =
    Function.updateITE (f ∘ g) a (f b) :=
  by
  funext x
  simp
  simp only [Function.updateITE]
  split_ifs
  · rfl
  · rfl


theorem Function.updateITE_comp_right
  {α β γ : Type}
  [DecidableEq α]
  [DecidableEq β]
  (f : α → β)
  (finv : β → α)
  (g : β → γ)
  (a : β)
  (b : γ)
  (h1 : finv ∘ f = id)
  (h2 : f ∘ finv = id) :
  (Function.updateITE g a b) ∘ f =
    Function.updateITE (g ∘ f) (finv a) b :=
  by
  funext x
  simp
  simp only [Function.updateITE]
  congr!
  constructor
  · intro a1
    simp only [← a1]
    obtain s1 := Function.left_id_left_inverse f finv h1
    simp only [Function.LeftInverse] at s1
    simp only [s1 x]
  · intro a1
    simp only [a1]
    obtain s1 := Function.right_id_right_inverse f finv h2
    simp only [Function.RightInverse] at s1
    simp only [Function.LeftInverse] at s1
    exact s1 a


theorem Function.updateITE_comp_right_injective
  {α β γ : Type}
  [DecidableEq α]
  [DecidableEq β]
  (f : α → β)
  (g : β → γ)
  (a : α)
  (b : γ)
  (h1 : Function.Injective f) :
  (Function.updateITE g (f a) b) ∘ f =
    Function.updateITE (g ∘ f) a b :=
  by
  simp only [Function.Injective] at h1

  funext x
  simp
  simp only [Function.updateITE]
  congr!
  constructor
  · apply h1
  · intro a1
    subst a1
    rfl


theorem Function.updateITE_comm
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a b : α)
  (c d : β)
  (h1 : ¬ a = b) :
  Function.updateITE (Function.updateITE f a d) b c =
    Function.updateITE (Function.updateITE f b c) a d :=
  by
  funext x
  simp only [Function.updateITE]
  split_ifs
  case _ c1 c2 =>
    subst c1 c2
    contradiction
  case _ | _ | _ =>
    rfl


theorem Function.updateITE_same
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a : α)
  (b : β)
  (h1 : f a = b) :
  Function.updateITE f a b = f :=
  by
    funext x
    simp only [Function.updateITE]
    split_ifs
    case _ c1 =>
      rw [c1]
      rw [h1]
    case _ c1 =>
      rfl


theorem Function.updateITE_idem
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a : α)
  (b c : β) :
  Function.updateITE (Function.updateITE f a b) a c =
    Function.updateITE f a c :=
  by
  funext x
  simp only [Function.updateITE]
  split_ifs
  · rfl
  · rfl


theorem Function.updateITE_id
  {α : Type}
  [DecidableEq α]
  (a : α) :
  Function.updateITE (id : α → α) a a = id :=
  by
  funext x
  simp only [Function.updateITE]
  split_ifs
  case _ c1 =>
    subst c1
    simp
  case _ =>
    rfl


theorem Function.updateITE_comm_id
  {α : Type}
  [DecidableEq α]
  (a b c : α)
  (h1 : ¬ a = b) :
  Function.updateITE (Function.updateITE id b c) a a =
    Function.updateITE id b c :=
  by
  funext x
  simp only [Function.updateITE]
  simp
  intro a1
  subst a1
  simp only [if_neg h1]


theorem Function.updateITE_coincide
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (a : α)
  (h1 : ∀ (x : α), ¬ x = a → f x = g x) :
  Function.updateITE f a (g a) = g :=
  by
  funext x
  simp only [Function.updateITE]
  split_ifs
  case _ c1 =>
    subst c1
    rfl
  case _ c1 =>
    exact h1 x c1


theorem Function.updateITE_not_mem_list
  {α β : Type}
  [DecidableEq α]
  (xs : List α)
  (f : α → β)
  (a : α)
  (b : β)
  (h1 : a ∉ xs) :
  xs.map (Function.updateITE f a b) = xs.map f :=
  by
  induction xs
  case nil =>
    simp
  case cons hd tl ih =>
    simp at h1
    push_neg at h1

    cases h1
    case intro h1_left h1_right =>
      simp
      simp only [Function.updateITE]
      split_ifs
      case pos c1 =>
        tauto
      case neg c1 =>
        constructor
        · rfl
        · intro a' a1
          split_ifs
          case pos c2 =>
            rw [c2] at a1
            contradiction
          case neg c2 =>
            rfl


theorem Function.updateITE_not_mem_set
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (S : Finset α)
  (f : α → β)
  (a : α)
  (b : β)
  (h1 : a ∉ S) :
  Finset.image (Function.updateITE f a b) S =
    Finset.image f S :=
  by
  induction S using Finset.induction_on
  case empty =>
    simp
  case insert S_a S_S _ S_ih =>
    simp at h1
    push_neg at h1

    cases h1
    case intro h1_left h1_right =>
      simp
      congr! 1
      · simp only [Function.updateITE]
        split_ifs
        case _ c1 =>
          subst c1
          contradiction
        case _ c1 =>
          rfl
      · exact S_ih h1_right


theorem Function.updateITE_symm
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a b : α)
  (c d : β)
  (h1 : ¬ a = b) :
  Function.updateITE (Function.updateITE f a c) b d =
    Function.updateITE (Function.updateITE f b d) a c :=
  by
  funext x
  simp only [Function.updateITE]
  by_cases c1 : x = a
  · by_cases c2 : x = b
    · subst c1
      subst c2
      contradiction
    · subst c1
      simp
      intro a1
      contradiction
  · by_cases c2 : x = b
    · subst c2
      simp
      simp only [if_neg c1]
    · simp only [if_neg c1]


lemma Function.updateITE_comp
  {α β : Type}
  [DecidableEq α]
  (a b c : α)
  (d : β)
  (f : α → α)
  (g : α → β)
  (h1 : f a = c → d = g (f a)) :
  Function.updateITE g c d (Function.updateITE f b c a) = Function.updateITE (g ∘ f) b d a :=
  by
  simp only [Function.updateITE]
  by_cases c1 : a = b
  · simp only [c1]
    simp
  · simp only [c1]
    simp
    exact h1


-- Function.updateListITE

theorem Function.updateListITE_comp
  {α β γ : Type}
  [DecidableEq α]
  (f : α → β)
  (g : β → γ)
  (xs : List α)
  (ys : List β) :
  g ∘ Function.updateListITE f xs ys =
    Function.updateListITE (g ∘ f) xs (ys.map g) :=
  by
  induction xs generalizing ys
  case nil =>
    simp only [Function.updateListITE]
  case cons _ xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp
      simp only [Function.updateListITE]
    case cons ys_hd ys_tl =>
      simp
      simp only [Function.updateListITE]
      simp only [← xs_ih]
      apply Function.updateITE_comp_left


theorem Function.updateListITE_mem'
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (xs ys : List α)
  (x : α)
  (h1 : f x = g x) :
  Function.updateListITE f xs (List.map f ys) x =
    Function.updateListITE g xs (List.map f ys) x :=
  by
  induction xs generalizing ys
  case nil =>
    simp only [Function.updateListITE]
    exact h1
  case cons _ xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp
      simp only [Function.updateListITE]
      exact h1
    case cons ys_hd ys_tl =>
      simp
      simp only [Function.updateListITE]
      simp only [Function.updateITE]
      split_ifs
      · rfl
      · exact xs_ih ys_tl


theorem Function.updateListITE_mem_eq_len
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (v : α)
  (xs : List α)
  (ys : List β)
  (h1 : v ∈ xs)
  (h2 : xs.length = ys.length) :
  Function.updateListITE f xs ys v =
    Function.updateListITE g xs ys v :=
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
      simp only [Function.updateListITE]
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


theorem Function.updateListITE_mem
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (v : α)
  (xs : List α)
  (ys : List β)
  (h1 : v ∈ xs)
  (h2 : f v = g v) :
  Function.updateListITE f xs ys v =
    Function.updateListITE g xs ys v :=
  by
  induction xs generalizing ys
  case nil =>
    contradiction
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp at h1

      simp only [Function.updateListITE]
      exact h2
    case cons ys_hd ys_tl =>
      simp at h1

      simp only [Function.updateListITE]
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


theorem Function.updateListITE_not_mem
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (v : α)
  (xs : List α)
  (ys : List β)
  (h1 : v ∉ xs) :
  Function.updateListITE f xs ys v = f v :=
  by
  induction xs generalizing ys
  case nil =>
    simp only [Function.updateListITE]
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [Function.updateListITE]
    case cons ys_hd ys_tl =>
      simp only [Function.updateListITE]
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


theorem Function.updateListITE_updateIte
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (xs : List α)
  (ys : List β)
  (x y : α)
  (z : β)
  (h1 : ¬ x = y) :
  Function.updateListITE (Function.updateITE f y z) xs ys x =
    Function.updateListITE f xs ys x :=
  by
  induction xs generalizing ys
  case nil =>
    simp only [Function.updateListITE]
    simp only [Function.updateITE]
    simp only [if_neg h1]
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [Function.updateListITE]
      simp only [Function.updateITE]
      simp only [if_neg h1]
    case cons ys_hd ys_tl =>
      simp only [Function.updateListITE]
      simp only [Function.updateITE]
      split_ifs
      case pos c1 =>
        rfl
      case neg c1 =>
        apply xs_ih


theorem Function.updateListITE_fun_coincide_mem_eq_len
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (xs ys : List α)
  (x : α)
  (h1 : ∀ (v : α), v ∈ ys → f v = g v)
  (h2 : x ∈ xs)
  (h3 : xs.length = ys.length):
  Function.updateListITE f xs (List.map f ys) x =
    Function.updateListITE g xs (List.map g ys) x :=
  by
  have s1 : List.map f ys = List.map g ys
  simp only [List.map_eq_map_iff]
  exact h1

  simp only [s1]
  apply Function.updateListITE_mem_eq_len
  · exact h2
  · simp
    exact h3


theorem Function.updateListITE_map_mem_ext
  {α β : Type}
  [DecidableEq α]
  (xs ys : List α)
  (f g h h' : α → β)
  (x : α)
  (h1 : ∀ (y : α), y ∈ ys → h y = h' y)
  (h2 : xs.length = ys.length)
  (h3 : x ∈ xs) :
  Function.updateListITE f xs (List.map h ys) x =
      Function.updateListITE g xs (List.map h' ys) x :=
  by
  have s1 : List.map h ys = List.map h' ys
  simp only [List.map_eq_map_iff]
  exact h1

  simp only [s1]
  apply Function.updateListITE_mem_eq_len
  · exact h3
  · simp
    exact h2


theorem Function.updateListITE_map_mem
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (xs : List α)
  (x : α)
  (h1 : x ∈ xs) :
  Function.updateListITE f xs (List.map g xs) x = g x :=
  by
  induction xs
  case nil =>
    simp at h1
  case cons hd tl ih =>
    simp at h1

    simp
    simp only [Function.updateListITE]
    simp only [Function.updateITE]
    split_ifs
    case _ c1 =>
      subst c1
      rfl
    case _ c1 =>
      tauto


theorem Function.updateListITE_map_updateIte
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
  Function.updateListITE f xs (List.map f ys) x =
  Function.updateListITE g xs (List.map (Function.updateITE f v a) ys) x :=
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

  exact Function.updateListITE_map_mem_ext xs ys f g f (Function.updateITE f v a) x s1 h2 h3


#lint
