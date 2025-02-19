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


#lint
