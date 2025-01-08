import MathlibExtra.Tactics
import MathlibExtra.FunctionUpdateITE


set_option autoImplicit false


theorem List.map_eq_self_iff
  {α : Type}
  (f : α → α)
  (xs : List α) :
  xs.map f = xs ↔
    ∀ (x : α), x ∈ xs → f x = x :=
  by
  induction xs
  case nil =>
    simp
  case cons hd tl ih =>
    simp
    intro _
    exact ih


lemma List.map_mem_id
  {α : Type}
  (f : α → α)
  (xs: List α)
  (h1: ∀ (x : α), x ∈ xs → f x = x) :
  xs.map f = xs :=
  by
  induction xs
  case nil =>
    simp
  case cons hd tl ih =>
    simp at h1
    cases h1
    case _ h1_left h1_right =>
      simp
      constructor
      · exact h1_left
      · exact ih h1_right


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
  simp only [Function.Injective] at h1

  simp only [Function.Injective]
  intro x1 x2 a1
  by_cases x1_a : x1 = a
  · by_cases x2_a : x2 = a
    · simp only [x1_a]
      simp only [x2_a]
    · by_cases x1_b : x1 = b
      · by_cases x2_b : x2 = b
        · simp only [x1_b]
          simp only [x2_b]
        · specialize h3 x2
          simp at h3
          specialize h3 x2_a x2_b
          simp only [← a1] at h3
          simp only [x1_a] at h3
          simp only [h2_left] at h3
          specialize h1 h3
          contradiction
      · by_cases x2_b : x2 = b
        · subst x1_a
          subst x2_b
          apply h1
          simp only [← h2_left]
          simp only [← h2_right]
          simp only [a1]
        · specialize h3 x2
          simp at h3
          specialize h3 x2_a x2_b
          simp only [← a1] at h3
          simp only [x1_a] at h3
          simp only [h2_left] at h3
          specialize h1 h3
          contradiction
  · by_cases x2_a : x2 = a
    · by_cases x1_b : x1 = b
      · subst x1_b
        subst x2_a
        apply h1
        simp only [← h2_left]
        simp only [← h2_right]
        simp only [a1]
      · by_cases x2_b : x2 = b
        · specialize h3 x1
          simp at h3
          specialize h3 x1_a x1_b
          simp only [a1] at h3
          simp only [x2_a] at h3
          simp only [h2_left] at h3
          simp only [← x2_b] at h3
          exact h1 h3
        · specialize h3 x1
          simp at h3
          specialize h3 x1_a x1_b
          simp only [a1] at h3
          simp only [x2_a] at h3
          simp only [h2_left] at h3
          specialize h1 h3
          contradiction
    · by_cases x1_b : x1 = b
      · by_cases x2_b : x2 = b
        · simp only [x1_b]
          simp only [x2_b]
        · specialize h3 x2
          simp at h3
          specialize h3 x2_a x2_b
          simp only [← a1] at h3
          simp only [x1_b] at h3
          simp only [h2_right] at h3
          specialize h1 h3
          contradiction
      · by_cases x2_b : x2 = b
        · specialize h3 x1
          simp at h3
          specialize h3 x1_a x1_b
          simp only [a1] at h3
          simp only [x2_b] at h3
          simp only [h2_right] at h3
          specialize h1 h3
          contradiction
        · have s1 : ¬ x1 = a ∧ ¬ x1 = b
          constructor
          · exact x1_a
          · exact x1_b

          have s2 : ¬ x2 = a ∧ ¬ x2 = b
          constructor
          · exact x2_a
          · exact x2_b

          apply h1
          simp only [h3 x1 s1]
          simp only [h3 x2 s2]
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
    have s1 : ys = []
    {
      apply List.eq_nil_of_length_eq_zero
      simp only [← h1]
      simp
    }
    simp only [s1]
    apply Exists.intro id
    constructor
    · simp only [List.InjOn]
      simp
    · simp
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp at h1
    case cons ys_hd ys_tl =>
      simp at h1
      simp at h2
      simp at h3

      cases h2
      case intro h2_left h2_right =>
        cases h3
        case intro h3_left h3_right =>
          simp
          specialize xs_ih ys_tl h1 h2_right h3_right

          apply Exists.elim xs_ih
          intro f a1
          clear xs_ih

          simp only [List.InjOn]
          cases a1
          case intro a1_left a1_right =>
            apply Exists.intro (Function.updateITE f xs_hd ys_hd)
            constructor
            · intro x1 x1_mem x2 x2_mem
              simp at x1_mem
              simp at x2_mem
              simp only [Function.updateITE]
              split_ifs
              case _ c1 c2 =>
                intro _
                simp only [c1]
                simp only [c2]
              case _ c1 c2 =>
                intro a2
                cases x2_mem
                case inl c3 =>
                  contradiction
                case inr c3 =>
                  obtain s1 := List.mem_map_of_mem f c3
                  simp only [a1_right] at s1
                  simp only [← a2] at s1
                  contradiction
              case _ c1 c2 =>
                intro a2
                cases x1_mem
                case inl c3 =>
                  contradiction
                case inr c3 =>
                  obtain s1 := List.mem_map_of_mem f c3
                  simp only [a1_right] at s1
                  simp only [a2] at s1
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
                    simp only [List.InjOn] at a1_left
                    apply a1_left x1_mem_right x2_mem_right a2
            · constructor
              · simp only [Function.updateITE]
                simp
              · simp only [← a1_right]
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
      · rw [c1]
        apply Exists.intro []
        apply Exists.intro []
        apply Exists.intro hd
        simp
      · specialize ih c1
        obtain ⟨xs, zs, y, eq⟩ := ih
        apply Exists.intro (hd :: xs)
        apply Exists.intro zs
        apply Exists.intro y
        simp
        simp at eq
        exact eq


lemma List.exists_mem_imp_exists_leftmost_mem
  {α : Type}
  (l : List α)
  (f : α → Prop)
  (h1 : ∃ (x : α), x ∈ l ∧ f x) :
  ∃ (ll : List α) (y : α) (rl : List α), l = ll ++ [y] ++ rl ∧
    f y ∧ ∀ (a : α), a ∈ ll → ¬ f a :=
  by
    induction l
    case nil =>
      simp at h1
    case cons hd tl ih =>
      simp at ih
      simp at h1
      simp
      by_cases c1 : f hd
      case pos =>
        apply Exists.intro []
        simp
        exact c1
      case neg =>
        cases h1
        case inl h1_left =>
          contradiction
        case inr h1_right =>
          obtain ⟨x, a1, a2⟩ := h1_right
          specialize ih x a1 a2
          obtain ⟨ll, y, ⟨rl, a3⟩, a4, a5⟩ := ih
          apply Exists.intro (hd :: ll)
          apply Exists.intro y
          constructor
          · apply Exists.intro rl
            simp
            exact a3
          · constructor
            · exact a4
            · simp
              exact ⟨c1, a5⟩


lemma List.exists_mem_imp_exists_rightmost_mem
  {α : Type}
  (l : List α)
  (f : α → Prop)
  (h1 : ∃ (x : α), x ∈ l ∧ f x) :
  ∃ (ll : List α) (y : α) (rl : List α), l = ll ++ [y] ++ rl ∧
    f y ∧ ∀ (a : α), a ∈ rl → ¬ f a :=
  by
    induction l
    case nil =>
      simp at h1
    case cons hd tl ih =>
      simp at ih
      simp at h1
      simp
      by_cases c1 : ∃ a ∈ tl, f a
      case pos =>
        obtain ⟨x, a1, a2⟩ := c1
        specialize ih x a1 a2
        obtain ⟨ll, y, rl, a3, a4, a5⟩ := ih
        apply Exists.intro (hd :: ll)
        apply Exists.intro y
        apply Exists.intro rl
        constructor
        · rw [a3]
          simp
        · exact ⟨a4, a5⟩
      case neg =>
        cases h1
        case inl h1_left =>
          apply Exists.intro []
          apply Exists.intro hd
          apply Exists.intro tl
          simp
          simp at c1
          exact ⟨h1_left, c1⟩
        case inr h1_right =>
          contradiction


-------------------------------------------------------------------------------

/-
protected def append : (xs ys : List α) → List α
  | [],    bs => bs
  | a::as, bs => a :: List.append as bs
-/


lemma List.length_nil_
  {α : Type} :
  ([] : List α).length = 0 := by
  unfold List.length
  real_rfl


lemma List.length_cons_
  {α : Type}
  (a : α)
  (as : List α) :
  (a :: as).length = as.length + 1 := by
  induction as generalizing a
  case nil =>
    unfold List.length
    rw [List.length_nil_]
  case cons hd tl ih =>
    unfold List.length
    specialize ih hd
    rw [ih]


lemma List.nil_append_
  {α : Type}
  (as : List α) :
  [] ++ as = as := by
  unfold_projs
  unfold List.append
  real_rfl


lemma List.cons_append_
  {α : Type}
  (a : α)
  (as bs : List α) :
  (a :: as) ++ bs = a :: (as ++ bs) := by
  unfold_projs
  conv =>
    lhs
    unfold List.append


lemma List.append_nil_
  {α : Type}
  (as : List α) :
  as ++ [] = as := by
  induction as
  case nil =>
    unfold_projs
    unfold List.append
    real_rfl
  case cons hd tl ih =>
    rw [List.cons_append_]
    rw [ih]


lemma List.length_append_
  {α : Type}
  (as bs : List α) :
  (as ++ bs).length = as.length + bs.length := by
  induction as
  case nil =>
    rw [List.nil_append_]
    rw [List.length_nil_]
    rw [Nat.add_comm]
    unfold_projs
    unfold Nat.add
    real_rfl
  case cons hd tl ih =>
    simp only [cons_append_, length_cons_]
    rw [ih]
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
      case _ =>
        simp at a1
        simp
        exact a1
      case _ hd tl =>
        simp at a1
    · simp
      intro a1 a2 a3
      rw [a1]
      rw [a2]
      rw [a3]
      simp


lemma rgr_r9
  {α : Type}
  (r : List α)
  (sym : α)
  (h1 : sym ∈ r) :
  ∃ r1 r2, r = r1 ++ [sym] ++ r2 :=
  by
    induction r
    case nil =>
      simp at h1
    case cons hd tl ih =>
      simp at h1
      cases h1
      case inl h1_left =>
        rw [h1_left]
        apply Exists.intro []
        apply Exists.intro tl
        simp
      case inr h1_right =>
        specialize ih h1_right
        obtain ⟨r1, r2, a1⟩ := ih
        apply Exists.intro (hd :: r1)
        apply Exists.intro r2
        rw [a1]
        simp


lemma rgr_r9b
  {α : Type}
  (r : List α)
  (sym : α)
  (h1 : ∃ (r1 r2 : List α), r = r1 ++ [sym] ++ r2) :
  sym ∈ r :=
  by
    obtain ⟨r1, r2, eq⟩ := h1
    rw [eq]
    simp


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
    rw [h1]
    simp


lemma append_eq_sing
  {α : Type}
  (l1 l2 : List α)
  (e : α) :
  (l1 ++ l2 = [e]) ↔ (l1 = [e]) ∧ (l2 = []) ∨ (l1 = []) ∧ (l2 = [e]) :=
  by
    cases l1
    case nil =>
      simp
    case cons hd tl =>
      simp
      simp only [and_assoc]


lemma list_r2
  {α : Type}
  (sl_1 sl_2 rhs : List α)
  (x : α)
  (h1 : sl_1 ++ rhs ++ sl_2 = [x])
  (h2 : ¬ rhs = []) :
  sl_1 = [] ∧ sl_2 = [] :=
  by
    simp only [append_eq_sing] at h1
    aesop





#lint
