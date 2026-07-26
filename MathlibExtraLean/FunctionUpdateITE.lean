import Mathlib.Tactic


set_option linter.style.docString false
set_option linter.style.emptyLine false


/--
  Specialized version of `Function.update` for non-dependent functions.
  `Function.updateITE f a b` := Replaces the value of `f` at `a` by `b`.
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

#eval Function.updateITE (fun _ => 0) 5 10 1
#eval Function.updateITE (fun _ => 0) 5 10 5


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

#eval Function.updateITE' (fun _ => 0) 5 10 1
#eval Function.updateITE' (fun _ => 0) 5 10 5


theorem Function.left_id_left_inverse
  {α β : Type}
  (f : α → β)
  (g : β → α)
  (h1 : g ∘ f = id) :
  Function.LeftInverse g f :=
  by
  unfold Function.LeftInverse
  intro x
  exact congrFun h1 x


theorem Function.right_id_right_inverse
  {α β : Type}
  (f : α → β)
  (g : β → α)
  (h1 : f ∘ g = id) :
  Function.RightInverse g f :=
  by
  unfold Function.RightInverse
  apply Function.left_id_left_inverse
  exact h1


-- Function.updateITE

theorem Function.updateITE_eq_Function.updateITE'
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (a : α)
  (b : β) :
  Function.updateITE f a b =
    Function.updateITE' f a b :=
  by
  funext x
  unfold Function.updateITE
  unfold Function.updateITE'
  split
  case isTrue c1 =>
    split
    case isTrue c2 =>
      apply Eq.refl
    case isFalse c2 =>
      rewrite [c1] at c2
      contradiction
  case isFalse c1 =>
    split
    case isTrue c2 =>
      rewrite [c2] at c1
      contradiction
    case isFalse c2 =>
      apply Eq.refl


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
  simp only [comp_apply]
  unfold Function.updateITE
  split
  case isTrue c1 =>
    apply Eq.refl
  case isFalse c1 =>
    simp only [comp_apply]


theorem Function.updateITE_comp_right
  {α β γ : Type}
  [DecidableEq α]
  [DecidableEq β]
  (f : α → β)
  (f_inv : β → α)
  (g : β → γ)
  (a : β)
  (b : γ)
  (h1 : f_inv ∘ f = id)
  (h2 : f ∘ f_inv = id) :
  (Function.updateITE g a b) ∘ f =
    Function.updateITE (g ∘ f) (f_inv a) b :=
  by
  funext x
  simp only [comp_apply]
  unfold Function.updateITE
  congr!
  constructor
  · intro a1
    rewrite [← a1]
    obtain s1 := Function.left_id_left_inverse f f_inv h1
    unfold Function.LeftInverse at s1
    rewrite [s1 x]
    apply Eq.refl
  · intro a1
    rewrite [a1]
    obtain s1 := Function.right_id_right_inverse f f_inv h2
    unfold Function.RightInverse at s1
    unfold Function.LeftInverse at s1
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
  unfold Function.Injective at h1

  funext x
  simp only [comp_apply]
  unfold Function.updateITE
  congr!
  constructor
  · apply h1
  · intro a1
    rewrite [a1]
    apply Eq.refl


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
  unfold Function.updateITE
  split
  case isTrue c1 =>
    split
    case isTrue c2 =>
      rewrite [← c1] at h1
      rewrite [← c2] at h1
      contradiction
    case isFalse c2 =>
      apply Eq.refl
  case isFalse c1 =>
    split
    case isTrue c2 =>
      apply Eq.refl
    case isFalse c2 =>
      apply Eq.refl


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
  unfold Function.updateITE
  split
  case isTrue c1 =>
    rewrite [c1]
    rewrite [h1]
    apply Eq.refl
  case isFalse c1 =>
    apply Eq.refl


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
  unfold Function.updateITE
  split
  case isTrue c1 =>
    apply Eq.refl
  case isFalse c1 =>
    apply Eq.refl


theorem Function.updateITE_id
  {α : Type}
  [DecidableEq α]
  (a : α) :
  Function.updateITE (id : α → α) a a = id :=
  by
  funext x
  unfold Function.updateITE
  split
  case isTrue c1 =>
    rewrite [c1]
    unfold id
    apply Eq.refl
  case isFalse c1 =>
    apply Eq.refl


theorem Function.updateITE_comm_id
  {α : Type}
  [DecidableEq α]
  (a b c : α)
  (h1 : ¬ a = b) :
  Function.updateITE (Function.updateITE id b c) a a =
    Function.updateITE id b c :=
  by
  funext x
  unfold Function.updateITE
  unfold id
  split
  case isTrue c1 =>
    split
    case isTrue c2 =>
      rewrite [← c1] at h1
      rewrite [← c2] at h1
      contradiction
    case isFalse c2 =>
      rewrite [c1]
      apply Eq.refl
  case isFalse c1 =>
    split
    case isTrue c2 =>
      apply Eq.refl
    case isFalse c2 =>
      apply Eq.refl


theorem Function.updateITE_coincide
  {α β : Type}
  [DecidableEq α]
  (f g : α → β)
  (a : α)
  (h1 : ∀ (x : α), ¬ x = a → f x = g x) :
  Function.updateITE f a (g a) = g :=
  by
  funext x
  unfold Function.updateITE
  split
  case isTrue c1 =>
    rewrite [c1]
    apply Eq.refl
  case isFalse c1 =>
    apply h1
    exact c1


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
    simp only [List.map_nil]
  case cons hd tl ih =>
    simp only [List.mem_cons] at h1
    simp only [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [List.map_cons, List.cons.injEq]
    constructor
    · unfold Function.updateITE
      split
      case isTrue c1 =>
        rewrite [c1] at h1_left
        contradiction
      case isFalse c1 =>
        apply Eq.refl
    · apply ih
      exact h1_right


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
    simp only [Finset.image_empty]
  case insert S_a S_S ih_1 ih_2 =>
    simp only [Finset.mem_insert] at h1
    simp only [not_or] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [Finset.image_insert]
    congr! 1
    · unfold Function.updateITE
      split
      case isTrue c1 =>
        rewrite [c1] at h1_left
        contradiction
      case isFalse c1 =>
        apply Eq.refl
    · exact ih_2 h1_right


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
  unfold Function.updateITE
  split
  case isTrue c1 =>
    split
    case isTrue c2 =>
      rewrite [← c1] at h1
      rewrite [← c2] at h1
      contradiction
    case isFalse c2 =>
      apply Eq.refl
  case isFalse c1 =>
    split
    case isTrue c2 =>
      apply Eq.refl
    case isFalse c2 =>
      apply Eq.refl


theorem Function.updateITE_comp
  {α β : Type}
  [DecidableEq α]
  (a b c : α)
  (d : β)
  (f : α → α)
  (g : α → β)
  (h1 : f a = c → d = g (f a)) :
  Function.updateITE g c d (Function.updateITE f b c a) = Function.updateITE (g ∘ f) b d a :=
  by
  unfold Function.updateITE
  split
  case isTrue c1 =>
    split
    case isTrue c2 =>
      apply Eq.refl
    case isFalse c2 =>
      contradiction
  case isFalse c1 =>
    split
    case isTrue c2 =>
      simp only [comp_apply]
      apply h1
      exact c2
    case isFalse c2 =>
      simp only [comp_apply]
