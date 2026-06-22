import Mathlib.Data.List.Basic
import Mathlib.Data.List.Zip
import Mathlib.Data.List.Perm.Basic

namespace RUXt

namespace List

/-- `Permutation_spec`: permutations preserve membership. -/
theorem perm_mem_iff {α : Type*} {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    ∀ x, x ∈ l₁ ↔ x ∈ l₂ :=
  fun _ => h.mem_iff

/-- `elem_of_subseteq`: membership is preserved by list inclusion. -/
theorem mem_of_subset {α : Type*} {l k : List α} {x : α} (hin : x ∈ l) (hsub : l ⊆ k) :
    x ∈ k :=
  hsub hin

/-- `zip_with_reverse`: `zipWith` of equal-length lists is, up to permutation,
`zipWith` of their reversals. -/
theorem zipWith_reverse_perm {α β γ : Type*} (f : α → β → γ) (l : List α) (k : List β)
    (h : l.length = k.length) :
    (List.zipWith f l k).Perm (List.zipWith f l.reverse k.reverse) := by
  rw [← List.reverse_zipWith h]
  exact (List.reverse_perm _).symm

end List

end RUXt
