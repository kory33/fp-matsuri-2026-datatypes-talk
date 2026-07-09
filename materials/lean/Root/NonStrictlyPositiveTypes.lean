import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Embedding.Basic

/-!
# Non-strictly positive type equations

This file records a diagonal obstruction to the type equation
`X ≃ (X → Y) → Y` when `Y` has two distinct elements `y₀ ≠ y₁`.

Idea: We can treat `y₀` and `y₁` as `false` and `true`, respectively.
      Then a subset `s : Set X` of `X` can be encoded as a characteristic function `χ_s : X → Y`
      by sending elements of `s` to `y₁` and elements of `X \ s` to `y₀`.
      This gives an injection `Set X ↪ (X → Y)`. Moreover,
      `(X → Y)` can be injected into `((X → Y) → Y)` by comparing two functions,
      returning `y₁` (standing for `true`) if they are equal and `y₀` (standing for `false`) otherwise.
      Finally, compose the equivalence to obtain a sequence of injections

        `Set X ↪ (X → Y) ↪ ((X → Y) → Y) ↪ X`,

      and this contradicts Cantor's theorem `Function.cantor_injective`.

This in particular implies that the hypothetical inductive definition:

```lean
inductive Bad where
  | mk : ((Bad → Y) → Y) → Bad
```

shall be rejected, since a priori we can't know whether `Y` has two distinct elements or not.
-/

namespace NonStrictlyPositiveTypes

universe u v

theorem not_equiv_continuation (X : Type u) (Y : Type v) (y₀ y₁ : Y) (hne : y₀ ≠ y₁) :
    ¬ Nonempty (X ≃ ((X → Y) → Y)) := by
  classical
  rintro ⟨e⟩

  let characteristic : Set X ↪ (X → Y) :=
    ⟨fun s x ↦ if x ∈ s then y₁ else y₀, by
      intro s t hst
      ext x
      by_cases hs : x ∈ s <;> by_cases ht : x ∈ t
      · exact iff_of_true hs ht
      · have := congr_fun hst x
        simp only [hs, ht, if_true, if_false] at this
        exact (hne this.symm).elim
      · have := congr_fun hst x
        simp only [hs, ht, if_true, if_false] at this
        exact (hne this).elim
      · exact iff_of_false hs ht⟩

  let singleton : (X → Y) ↪ ((X → Y) → Y) :=
    ⟨fun f g ↦ if g = f then y₁ else y₀, by
      intro f g hfg
      by_contra hnefg
      have := congr_fun hfg f
      simp only [if_true, hnefg, if_false] at this
      exact hne this.symm⟩

  let cantorEmbedding : Set X ↪ X := characteristic.trans (singleton.trans e.symm.toEmbedding)
  exact Function.cantor_injective cantorEmbedding cantorEmbedding.injective

/-- If `Y` is a singleton, the type equation `X ≃ (X → Y) → Y` forces `X` to be a singleton as well. -/
theorem unique_of_equiv_continuation (X : Type u) (Y : Type v) [Unique Y]
    (h : Nonempty (X ≃ ((X → Y) → Y))) : Nonempty (Unique X) := by
  let e := h.some
  let x₀ := e.symm (fun _ ↦ default)
  refine ⟨⟨⟨x₀⟩, ?_⟩⟩
  intro x
  apply e.injective
  funext f
  exact Subsingleton.elim _ _

/-- If `Y` is empty, every solution of `X ≃ (X → Y) → Y` is either empty or a
singleton. -/
theorem empty_or_unique_of_equiv_continuation (X : Type u) (Y : Type v) [IsEmpty Y]
    (h : Nonempty (X ≃ ((X → Y) → Y))) : IsEmpty X ∨ Nonempty (Unique X) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact Or.inl hX
  · right
    letI : Nonempty X := hX
    letI : IsEmpty (X → Y) := inferInstance
    letI : Unique ((X → Y) → Y) := inferInstance
    let e := h.some
    let x₀ := e.symm default
    refine ⟨⟨⟨x₀⟩, ?_⟩⟩
    intro x
    apply e.injective
    exact Subsingleton.elim _ _

/-- When `Y` is empty, the empty type satisfies the type equation. -/
def emptyEquivContinuationEmpty : Empty ≃ ((Empty → Empty) → Empty) :=
  Equiv.equivOfIsEmpty _ _

/-- When `Y` is empty, a singleton type also satisfies the type equation. -/
def punitEquivContinuationEmpty : Unit ≃ ((Unit → Empty) → Empty) :=
  Equiv.ofUnique _ _

end NonStrictlyPositiveTypes
