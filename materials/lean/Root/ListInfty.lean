namespace ListInfty

def CoList (α : Type u) : Type u :=
  { f : Nat → Option α // ∀ n, f n = none → f (n + 1) = none }

def nil : CoList α :=
  ⟨fun _ ↦ none, by simp⟩

def cons (a : α) (xs : CoList α) : CoList α :=
  ⟨fun
    | 0 => some a
    | n + 1 => xs.1 n,
    by
      intro n h
      cases n with
      | zero => simp at h
      | succ n => simpa using xs.2 n h⟩

def repeatCoList (a : α) : CoList α :=
  ⟨fun _ ↦ some a, by simp⟩

@[simp]
theorem cons_repeatCoList (a : α) : cons a (repeatCoList a) = repeatCoList a := by
  apply Subtype.ext
  funext n
  cases n <;> rfl

abbrev FoldCoList.{u} :=
  {α β : Type u} → (α → β → β) → β → CoList α → β

/-- The type of folds is inhabited, but this function does not satisfy the `cons` law in general. -/
def foldCoListIgnore : FoldCoList := fun _ z _ ↦ z

/-- The usual computation laws expected of a fold on `CoList`. -/
structure LawfulFoldCoList (foldCoList : FoldCoList) : Prop where
  nil (f : α → β → β) (z : β) : foldCoList f z nil = z
  cons (f : α → β → β) (z : β) (a : α) (xs : CoList α) :
    foldCoList f z (ListInfty.cons a xs) = f a (foldCoList f z xs)

/-- No total polymorphic fold on possibly infinite lists can satisfy the usual fold laws. -/
theorem not_lawfulFoldCoList (foldCoList : FoldCoList) : ¬ LawfulFoldCoList foldCoList := by
  intro lawful
  let a : ULift Unit := ULift.up ()
  let z : ULift Nat := ULift.up 0
  have h := lawful.cons (fun (_ : ULift Unit) n ↦ ULift.up (n.down + 1)) z a
    (repeatCoList a)
  simp only [cons_repeatCoList] at h
  have hn := congrArg ULift.down h
  change _ = _ + 1 at hn
  exact (Nat.ne_of_lt (Nat.lt_succ_self _)) hn

/-- Equivalently, a lawful total fold on `CoList` does not exist. -/
theorem no_lawfulFoldCoList : ¬ ∃ foldCoList : FoldCoList, LawfulFoldCoList foldCoList := by
  rintro ⟨foldCoList, lawful⟩
  exact not_lawfulFoldCoList foldCoList lawful

private def unfoldCoListImpl {β : Type u} (f : β → Option (α × β)) : Nat → β → Option α
  | 0, b => (f b).map Prod.fst
  | n + 1, b => (f b).bind (fun (_, b') ↦ unfoldCoListImpl f n b')

private theorem unfoldCoListNonincreasing {β : Type u} (f : β → Option (α × β)) (n : Nat)
    (b : β) (h : unfoldCoListImpl f n b = none) : unfoldCoListImpl f (n + 1) b = none := by
  induction n generalizing b with
  | zero => simp_all [unfoldCoListImpl]
  | succ n ih =>
    cases hfb : f b with
    | none => simp [unfoldCoListImpl, hfb]
    | some result =>
      obtain ⟨a, b'⟩ := result
      have tailStopped : unfoldCoListImpl f n b' = none := by
        simpa only [unfoldCoListImpl, hfb, Option.bind_some] using h
      rw [unfoldCoListImpl, hfb, Option.bind_some]
      exact ih b' tailStopped

def unfoldCoList {β : Type u} (f : β → Option (α × β)) (b : β) : CoList α :=
  ⟨fun n ↦ unfoldCoListImpl f n b, fun n ↦ unfoldCoListNonincreasing f n b⟩

end ListInfty
