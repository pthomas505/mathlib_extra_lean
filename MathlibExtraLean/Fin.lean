import Mathlib.Data.List.OfFn


set_option autoImplicit false


def Fin.zipWith
  {α β γ : Type}
  (f : α → β → γ)
  (n : ℕ)
  (xs_fn : Fin n → α)
  (ys_fn : Fin n → β) :
  Fin n → γ :=
  fun (i : Fin n) => f (xs_fn i) (ys_fn i)


theorem list_of_fn_fin_zip_with_eq_list_zip_with_list_of_fn
  {α β γ : Type}
  (f : α → β → γ)
  (n : ℕ)
  (xs_fn : Fin n → α)
  (ys_fn : Fin n → β) :
  List.ofFn (Fin.zipWith f n xs_fn ys_fn) =
    List.zipWith f (List.ofFn xs_fn) (List.ofFn ys_fn) :=
  by
  unfold Fin.zipWith
  induction n
  case zero =>
    simp only [List.ofFn_zero]
    unfold List.zipWith
    rfl
  case succ m ih =>
    simp only [List.ofFn_succ]
    unfold List.zipWith
    congr
    exact ih (fun (i : Fin m) => xs_fn i.succ) (fun (i : Fin m) => ys_fn i.succ)


theorem list_of_fn_fin_zip_with_eq_len_list_to_fn_eq_list_zip_with
  {α β γ : Type}
  (f : α → β → γ)
  (xs : List α)
  (ys : List β)
  (h1 : xs.length = ys.length) :
  List.ofFn (Fin.zipWith f xs.length (fun (i : Fin xs.length) => xs[i]) (fun (i : Fin xs.length) => ys[i])) = List.zipWith f xs ys :=
  by
  unfold Fin.zipWith
  induction xs generalizing ys
  case nil =>
    simp only [List.length_nil, List.ofFn_zero, List.zipWith_nil_left]
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.length_cons, List.length_nil] at h1
      contradiction
    case cons ys_hd ys_tl =>
      simp only [List.length_cons] at h1
      simp only [Nat.succ.injEq] at h1

      simp only [List.length_cons, Fin.getElem_fin, List.ofFn_succ, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ, List.zipWith_cons_cons]
      congr
      apply xs_ih
      exact h1


lemma exists_list_of_fn_fin_zip_with_eq_len_eq_list_zip_with_and_list_of_fn_eq_list
  {α β γ : Type}
  (f : α → β → γ)
  (xs : List α)
  (ys : List β)
  (h1 : xs.length = ys.length) :
  ∃ (n : Nat) (xs_fn : Fin n → α) (ys_fn : Fin n → β),
    List.ofFn (Fin.zipWith f n xs_fn ys_fn) = List.zipWith f xs ys ∧
    List.ofFn xs_fn = xs ∧
    List.ofFn ys_fn = ys :=
  by
  apply Exists.intro (xs.length)
  apply Exists.intro (fun (i : Fin xs.length) => xs[i])
  apply Exists.intro (fun (i : Fin xs.length) => ys[i])
  constructor
  · apply list_of_fn_fin_zip_with_eq_len_list_to_fn_eq_list_zip_with
    exact h1
  · constructor
    . simp only [Fin.getElem_fin, List.ofFn_getElem]
    · simp only [h1]
      simp only [Fin.getElem_fin, Fin.coe_cast, List.ofFn_getElem]


-------------------------------------------------------------------------------


theorem list_of_fn_fin_zip_with_min_len_list_to_fn_cons
  {α β γ : Type}
  (f : α → β → γ)
  (xs_hd : α)
  (xs_tl : List α)
  (ys_hd : β)
  (ys_tl : List β) :
  List.ofFn (Fin.zipWith f (min (xs_hd :: xs_tl).length (ys_hd :: ys_tl).length) (fun i => (xs_hd :: xs_tl)[i]) (fun i => (ys_hd :: ys_tl)[i])) = f xs_hd ys_hd :: List.ofFn (fun (i : Fin (min xs_tl.length ys_tl.length)) => f xs_tl[i] ys_tl[i]) :=
  by
  unfold Fin.zipWith
  simp only [List.length_cons]
  simp only [Fin.getElem_fin]

  apply List.ext_get?
  intro n
  simp only [List.get?_eq_getElem?, List.getElem?_ofFn]
  cases n
  case _ =>
    split_ifs
    case pos c1 =>
      simp only [List.getElem_cons_zero, List.length_cons, List.length_ofFn, Nat.zero_lt_succ, List.getElem?_eq_getElem]
    case neg c1 =>
      simp only [lt_inf_iff, Nat.zero_lt_succ] at c1
      tauto
  case _ n =>
    simp only [lt_inf_iff, Nat.add_lt_add_iff_right, List.getElem_cons_succ, List.getElem?_cons_succ, List.getElem?_ofFn]


lemma list_of_fn_fin_zip_with_min_len_list_to_fn_eq_list_zip_with
  {α β γ : Type}
  (f : α → β → γ)
  (xs : List α)
  (ys : List β) :
  List.ofFn (Fin.zipWith f (min xs.length ys.length) (fun (i : Fin (min xs.length ys.length)) => xs[i]) (fun (i : Fin (min xs.length ys.length)) => ys[i])) = List.zipWith f xs ys :=
  by
  induction xs generalizing ys
  case nil =>
    simp
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.length_cons, List.length_nil, List.ofFn_zero, List.zipWith_nil_right]
    case cons ys_hd ys_tl =>
      simp only [List.zipWith]
      rewrite [list_of_fn_fin_zip_with_min_len_list_to_fn_cons]
      congr
      apply xs_ih
