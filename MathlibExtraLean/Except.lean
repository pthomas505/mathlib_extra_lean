import Mathlib.Tactic


set_option autoImplicit false


theorem Except.bind_eq_ok
  {ε α β : Type}
  (x : Except ε α)
  (f : α → Except ε β)
  (a : β) :
  (Except.bind x f = .ok a) ↔ ∃ (b : α), x = .ok b ∧ f b = .ok a :=
  by
  cases x
  case error x =>
    simp only [Except.bind]
    constructor
    · intro a1
      contradiction
    · intro a1
      obtain ⟨b, ⟨a1_left, a1_right⟩⟩ := a1
      contradiction
  case ok x =>
    simp only [Except.bind]
    constructor
    · intro a1
      apply Exists.intro x
      constructor
      · rfl
      · exact a1
    · intro a1
      obtain ⟨b, ⟨a1_left, a1_right⟩⟩ := a1
      simp only [ok.injEq] at a1_left
      rewrite [a1_left]
      exact a1_right


def Option.toExcept
  {α : Type}
  (opt : Option α)
  (message : String) :
  Except String α :=
  if h : Option.isSome opt
  then
    let a := Option.get opt h
    Except.ok a
  else Except.error message
