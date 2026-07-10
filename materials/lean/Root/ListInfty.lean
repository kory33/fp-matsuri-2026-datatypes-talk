namespace ListInfty

def CoList (α : Type u) : Type u :=
  { f : Nat → Option α // ∀ n, f n = none → f (n + 1) = none }

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
