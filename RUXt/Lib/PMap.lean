/-
Partial maps as `Option`-valued functions.

This is the Lean counterpart of the finite maps (`gmap`) from `stdpp` on which the
Rocq development is built. Finiteness of the maps plays no role anywhere in the
RUXt formalisation — allocation is specified relationally, and no fresh location
is ever computed — so we use the simpler, extensional model of partial maps as
plain functions `α → Option β`. Union is left-biased, exactly as for `gmap`.

Besides the general theory, this file ports the auxiliary lemmas of
`theories/lib/gmap.v`.
-/
import Mathlib.Data.Set.Insert
import Mathlib.Order.SetNotation

namespace RUXt

/-- Partial maps from `α` to `β`, the counterpart of `stdpp`'s `gmap α β`. -/
def PMap (α : Type*) (β : Type*) := α → Option β

namespace PMap

variable {α : Type*} {β : Type*}

instance : EmptyCollection (PMap α β) := ⟨fun _ => none⟩

/-- Left-biased union, as for `gmap`. -/
protected def union (m₁ m₂ : PMap α β) : PMap α β :=
  fun a => match m₁ a with | some b => some b | none => m₂ a

instance : Union (PMap α β) := ⟨PMap.union⟩

/-- `m.insert a b` maps `a` to `b` and is `m` elsewhere (stdpp's `<[a := b]> m`). -/
def insert [DecidableEq α] (a : α) (b : β) (m : PMap α β) : PMap α β :=
  fun a' => if a' = a then some b else m a'

/-- The singleton map (stdpp's `{[a := b]}`). -/
def singleton [DecidableEq α] (a : α) (b : β) : PMap α β :=
  insert a b ∅

/-- Remove a key (stdpp's `delete`). -/
def delete [DecidableEq α] (a : α) (m : PMap α β) : PMap α β :=
  fun a' => if a' = a then none else m a'

/-- The domain of a partial map, as a set. -/
def dom (m : PMap α β) : Set α := {a | ∃ b, m a = some b}

/-- Two maps are disjoint when their domains are (stdpp's `##ₘ`). -/
protected def Disjoint (m₁ m₂ : PMap α β) : Prop :=
  ∀ a, m₁ a = none ∨ m₂ a = none

@[inherit_doc] scoped infixl:50 " ##ₘ " => PMap.Disjoint

/-- Map inclusion: `m₁ ⊆ m₂` iff `m₂` agrees with `m₁` wherever `m₁` is defined. -/
instance : HasSubset (PMap α β) := ⟨fun m₁ m₂ => ∀ a b, m₁ a = some b → m₂ a = some b⟩

/-! ### Pointwise characterisations -/

@[ext] theorem ext {m₁ m₂ : PMap α β} (h : ∀ a, m₁ a = m₂ a) : m₁ = m₂ := funext h

@[simp] theorem empty_apply (a : α) : (∅ : PMap α β) a = none := rfl

@[simp, grind =] theorem union_apply (m₁ m₂ : PMap α β) (a : α) :
    (m₁ ∪ m₂) a = match m₁ a with | some b => some b | none => m₂ a := rfl

@[simp, grind =] theorem insert_apply [DecidableEq α] (a : α) (b : β) (m : PMap α β) (a' : α) :
    insert a b m a' = if a' = a then some b else m a' := rfl

@[simp, grind =] theorem singleton_apply [DecidableEq α] (a : α) (b : β) (a' : α) :
    singleton a b a' = if a' = a then some b else none := rfl

@[simp, grind =] theorem delete_apply [DecidableEq α] (a : α) (m : PMap α β) (a' : α) :
    delete a m a' = if a' = a then none else m a' := rfl

@[simp, grind =] theorem mem_dom {m : PMap α β} {a : α} : a ∈ dom m ↔ ∃ b, m a = some b :=
  Iff.rfl

@[simp, grind =] theorem not_mem_dom {m : PMap α β} {a : α} : a ∉ dom m ↔ m a = none := by
  simp [dom, Option.eq_none_iff_forall_ne_some]

@[grind =] theorem disjoint_def {m₁ m₂ : PMap α β} :
    m₁ ##ₘ m₂ ↔ ∀ a, m₁ a = none ∨ m₂ a = none := Iff.rfl

@[grind =] theorem subset_def {m₁ m₂ : PMap α β} :
    m₁ ⊆ m₂ ↔ ∀ a b, m₁ a = some b → m₂ a = some b := Iff.rfl

/-! ### Disjointness -/

theorem Disjoint.symm {m₁ m₂ : PMap α β} (h : m₁ ##ₘ m₂) : m₂ ##ₘ m₁ :=
  fun a => (h a).symm

theorem disjoint_comm {m₁ m₂ : PMap α β} : m₁ ##ₘ m₂ ↔ m₂ ##ₘ m₁ :=
  ⟨Disjoint.symm, Disjoint.symm⟩

@[simp] theorem disjoint_empty_l (m : PMap α β) : (∅ : PMap α β) ##ₘ m :=
  fun _ => Or.inl rfl

@[simp] theorem disjoint_empty_r (m : PMap α β) : m ##ₘ (∅ : PMap α β) :=
  fun _ => Or.inr rfl

/-- stdpp's `map_disjoint_Some_l`. -/
theorem Disjoint.some_l {m₁ m₂ : PMap α β} {a : α} {b : β}
    (h : m₁ ##ₘ m₂) (ha : m₁ a = some b) : m₂ a = none := by
  rcases h a with h' | h' <;> grind

/-- stdpp's `map_disjoint_Some_r`. -/
theorem Disjoint.some_r {m₁ m₂ : PMap α β} {a : α} {b : β}
    (h : m₁ ##ₘ m₂) (ha : m₂ a = some b) : m₁ a = none :=
  h.symm.some_l ha

/-- stdpp's `map_disjoint_insert_l`. -/
@[simp] theorem disjoint_insert_l [DecidableEq α] {m₁ m₂ : PMap α β} {a : α} {b : β} :
    insert a b m₁ ##ₘ m₂ ↔ m₂ a = none ∧ m₁ ##ₘ m₂ := by
  constructor
  · intro h
    refine ⟨by have := h a; grind, fun a' => by have := h a'; grind⟩
  · intro ⟨h₁, h₂⟩ a'
    have := h₂ a'; grind

/-- stdpp's `map_disjoint_insert_r`. -/
@[simp] theorem disjoint_insert_r [DecidableEq α] {m₁ m₂ : PMap α β} {a : α} {b : β} :
    m₁ ##ₘ insert a b m₂ ↔ m₁ a = none ∧ m₁ ##ₘ m₂ := by
  rw [disjoint_comm, disjoint_insert_l, disjoint_comm]

/-- stdpp's `map_disjoint_singleton_l`. -/
@[simp] theorem disjoint_singleton_l [DecidableEq α] {m : PMap α β} {a : α} {b : β} :
    singleton a b ##ₘ m ↔ m a = none := by
  simp [singleton]

/-- stdpp's `map_disjoint_singleton_r`. -/
@[simp] theorem disjoint_singleton_r [DecidableEq α] {m : PMap α β} {a : α} {b : β} :
    m ##ₘ singleton a b ↔ m a = none := by
  rw [disjoint_comm]; simp

/-- stdpp's `map_disjoint_union_l`. -/
@[simp] theorem disjoint_union_l {m₁ m₂ m₃ : PMap α β} :
    m₁ ∪ m₂ ##ₘ m₃ ↔ (m₁ ##ₘ m₃) ∧ (m₂ ##ₘ m₃) := by
  constructor
  · intro h
    exact ⟨fun a => by have := h a; grind, fun a => by have := h a; grind⟩
  · intro ⟨h₁, h₂⟩ a
    have := h₁ a; have := h₂ a; grind

/-- stdpp's `map_disjoint_union_r`. -/
@[simp] theorem disjoint_union_r {m₁ m₂ m₃ : PMap α β} :
    m₁ ##ₘ m₂ ∪ m₃ ↔ (m₁ ##ₘ m₂) ∧ (m₁ ##ₘ m₃) := by
  rw [disjoint_comm, disjoint_union_l, disjoint_comm (m₂ := m₁), disjoint_comm (m₂ := m₁)]

/-! ### Union -/

@[simp] theorem empty_union (m : PMap α β) : ∅ ∪ m = m := by
  ext a; rfl

@[simp] theorem union_empty (m : PMap α β) : m ∪ ∅ = m := by
  ext a; cases h : m a <;> simp [h]

theorem union_assoc (m₁ m₂ m₃ : PMap α β) : m₁ ∪ m₂ ∪ m₃ = m₁ ∪ (m₂ ∪ m₃) := by
  ext a; grind

/-- stdpp's `map_union_comm`: union of disjoint maps is commutative. -/
theorem union_comm {m₁ m₂ : PMap α β} (h : m₁ ##ₘ m₂) : m₁ ∪ m₂ = m₂ ∪ m₁ := by
  ext a; have := h a; grind

/-- stdpp's `lookup_union_Some_raw`. -/
theorem union_apply_eq_some {m₁ m₂ : PMap α β} {a : α} {b : β} :
    (m₁ ∪ m₂) a = some b ↔ m₁ a = some b ∨ (m₁ a = none ∧ m₂ a = some b) := by
  grind

/-- stdpp's `lookup_union_Some_l`. -/
theorem union_apply_some_l {m₁ m₂ : PMap α β} {a : α} {b : β} (h : m₁ a = some b) :
    (m₁ ∪ m₂) a = some b := by grind

/-- stdpp's `lookup_union_r`. -/
theorem union_apply_none_l {m₁ m₂ : PMap α β} {a : α} (h : m₁ a = none) :
    (m₁ ∪ m₂) a = m₂ a := by grind

/-- stdpp's `lookup_union_Some_inv_l`. -/
theorem union_apply_some_inv_l {m₁ m₂ : PMap α β} {a : α} {b : β}
    (h : (m₁ ∪ m₂) a = some b) (h₂ : m₂ a = none) : m₁ a = some b := by grind

/-- stdpp's `lookup_union_Some_inv_r`. -/
theorem union_apply_some_inv_r {m₁ m₂ : PMap α β} {a : α} {b : β}
    (h : (m₁ ∪ m₂) a = some b) (h₁ : m₁ a = none) : m₂ a = some b := by grind

@[simp] theorem dom_union (m₁ m₂ : PMap α β) : dom (m₁ ∪ m₂) = dom m₁ ∪ dom m₂ := by
  ext a
  simp only [dom, union_apply, Set.mem_union, Set.mem_setOf_eq]
  grind

/-- stdpp's `insert_union_l`. -/
theorem insert_union_l [DecidableEq α] (a : α) (b : β) (m₁ m₂ : PMap α β) :
    insert a b m₁ ∪ m₂ = insert a b (m₁ ∪ m₂) := by
  ext a'; grind

/-- stdpp's `insert_union_singleton_l`. -/
theorem insert_eq_singleton_union [DecidableEq α] (a : α) (b : β) (m : PMap α β) :
    insert a b m = singleton a b ∪ m := by
  ext a'; grind

/-! ### Insert, singleton, delete -/

@[simp] theorem insert_apply_self [DecidableEq α] (a : α) (b : β) (m : PMap α β) :
    insert a b m a = some b := by grind

theorem insert_apply_ne [DecidableEq α] {a a' : α} (b : β) (m : PMap α β) (h : a' ≠ a) :
    insert a b m a' = m a' := by grind

/-- stdpp's `insert_insert`. -/
@[simp] theorem insert_insert [DecidableEq α] (a : α) (b b' : β) (m : PMap α β) :
    insert a b (insert a b' m) = insert a b m := by
  ext a'; grind

/-- stdpp's `insert_singleton`. -/
@[simp] theorem insert_singleton [DecidableEq α] (a : α) (b b' : β) :
    insert a b (singleton a b') = singleton a b := by
  simp [singleton]

/-- stdpp's `insert_commute`. -/
theorem insert_comm [DecidableEq α] {a a' : α} (h : a ≠ a') (b b' : β) (m : PMap α β) :
    insert a b (insert a' b' m) = insert a' b' (insert a b m) := by
  ext a''; grind

/-- stdpp's `insert_id`. -/
theorem insert_id [DecidableEq α] {a : α} {b : β} {m : PMap α β} (h : m a = some b) :
    insert a b m = m := by
  ext a'; grind

/-- stdpp's `insert_delete_insert`. -/
@[simp] theorem insert_delete [DecidableEq α] (a : α) (b : β) (m : PMap α β) :
    insert a b (delete a m) = insert a b m := by
  ext a'; grind

@[simp] theorem delete_apply_self [DecidableEq α] (a : α) (m : PMap α β) :
    delete a m a = none := by grind

@[simp] theorem dom_insert [DecidableEq α] (a : α) (b : β) (m : PMap α β) :
    dom (insert a b m) = {a} ∪ dom m := by
  ext a'; by_cases h : a' = a <;> simp [dom, h]

@[simp] theorem dom_empty : dom (∅ : PMap α β) = ∅ := by
  ext a; simp [dom]

@[simp] theorem dom_singleton [DecidableEq α] (a : α) (b : β) :
    dom (singleton a b : PMap α β) = {a} := by
  ext a'; by_cases h : a' = a <;> simp [dom, h]

/-- Decompose a map at a defined key: `m = {[a := b]} ∪ delete a m`. -/
theorem eq_singleton_union_delete [DecidableEq α] {m : PMap α β} {a : α} {b : β}
    (h : m a = some b) : m = singleton a b ∪ delete a m := by
  ext a'; grind

theorem disjoint_singleton_delete [DecidableEq α] (m : PMap α β) (a : α) (b : β) :
    singleton a b ##ₘ delete a m := by
  intro a'; grind

/-! ### Inclusion -/

@[simp] theorem empty_subset (m : PMap α β) : (∅ : PMap α β) ⊆ m :=
  fun _ _ h => by simp at h

theorem subset_refl (m : PMap α β) : m ⊆ m := fun _ _ h => h

theorem subset_apply {m₁ m₂ : PMap α β} (h : m₁ ⊆ m₂) {a : α} {b : β}
    (ha : m₁ a = some b) : m₂ a = some b := h a b ha

/-- stdpp's `insert_mono`. -/
theorem insert_mono [DecidableEq α] {m₁ m₂ : PMap α β} (a : α) (b : β) (h : m₁ ⊆ m₂) :
    insert a b m₁ ⊆ insert a b m₂ := by
  intro a' b'; have := subset_def.mp h a' b'; grind

/-! ### Ports of `theories/lib/gmap.v` -/

/-- `map_disjoint_insert_singleton_l`. -/
theorem disjoint_insert_singleton_l [DecidableEq α] {m : PMap α β} {a : α} (x y z : β) :
    insert a x (singleton a y) ##ₘ m ↔ singleton a z ##ₘ m := by
  simp

/-- `map_disjoint_insert_singleton_r`. -/
theorem disjoint_insert_singleton_r [DecidableEq α] {m : PMap α β} {a : α} (x y z : β) :
    m ##ₘ insert a x (singleton a y) ↔ m ##ₘ singleton a z := by
  simp

/-- `map_disjoint_Some_insert`. -/
theorem disjoint_some_insert [DecidableEq α] {m₁ m₂ : PMap α β} {a : α} {x : β} (y : β)
    (h : m₁ a = some x) (hdisj : m₁ ##ₘ m₂) : insert a y m₁ ##ₘ m₂ := by
  simp only [disjoint_insert_l]
  exact ⟨hdisj.some_l h, hdisj⟩

/-- `map_union_dom`. -/
theorem union_dom {m₁ m₂ : PMap α β} {a : α}
    (h : ∃ b, (m₁ ∪ m₂) a = some b) (hnone : m₁ a = none) : a ∈ dom m₂ := by
  grind

/-- `map_disjoint_union_insert`. -/
theorem disjoint_union_insert [DecidableEq α] {m₁ m₂ : PMap α β} {a : α} (x : β)
    (hdisj : m₁ ##ₘ m₂) (hnin : a ∉ dom (m₁ ∪ m₂)) : insert a x m₁ ##ₘ m₂ := by
  simp only [not_mem_dom, union_apply] at hnin
  simp only [disjoint_insert_l]
  grind

/-- `map_union_id_l`. -/
theorem union_id_l (m : PMap α β) : m = ∅ ∪ m := by simp

/-- `map_union_id_r`. -/
theorem union_id_r (m : PMap α β) : m = m ∪ ∅ := by simp

end PMap

end RUXt
