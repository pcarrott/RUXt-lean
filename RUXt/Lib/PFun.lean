import Mathlib.Data.PFun

namespace RUXt

/-- Partial maps from `α` to `β`, realised as an extension of Mathlib's partial
functions `PFun` (`α →. β`). The extra structure (`∅`, `∪`, `insert`,
`singleton`, `dom`, disjointness and inclusion) is what is needed to model
heaps in the rest of the development. -/
def PFun (α : Type*) (β : Type*) := α →. β

namespace PFun

open Classical

variable {α : Type*} {β : Type*}

instance : EmptyCollection (PFun α β) := ⟨fun _ => Part.none⟩

/-- Left-biased union. Because `PFun` has a `Prop`-valued domain this is defined
classically and is therefore `noncomputable`. -/
protected noncomputable def union (m₁ m₂ : PFun α β) : PFun α β :=
  fun a => if (m₁ a).Dom then m₁ a else m₂ a

noncomputable instance : Union (PFun α β) := ⟨PFun.union⟩

/-- `m.insert a b` maps `a` to `b` and is `m` elsewhere. -/
def insert [DecidableEq α] (a : α) (b : β) (m : PFun α β) : PFun α β :=
  fun a' => if a' = a then Part.some b else m a'

/-- The singleton map. -/
def singleton [DecidableEq α] (a : α) (b : β) : PFun α β := insert a b ∅

/-- The domain of a partial map, as a set. -/
def dom (m : PFun α β) : Set α := {a | (m a).Dom}

/-- Two maps are disjoint when their domains are. -/
protected def Disjoint (m₁ m₂ : PFun α β) : Prop :=
  ∀ a, m₁ a = Part.none ∨ m₂ a = Part.none

@[inherit_doc] scoped infixl:50 " ##ₘ " => PFun.Disjoint

/-- Map inclusion: `m₁ ⊆ m₂` iff `m₂` agrees with `m₁` wherever `m₁` is defined. -/
instance : HasSubset (PFun α β) :=
  ⟨fun m₁ m₂ => ∀ a b, m₁ a = Part.some b → m₂ a = Part.some b⟩

/-! ### Pointwise characterisations -/

@[ext] theorem ext {m₁ m₂ : PFun α β} (h : ∀ a, m₁ a = m₂ a) : m₁ = m₂ := funext h

@[simp] theorem empty_apply (a : α) : (∅ : PFun α β) a = Part.none := rfl

theorem union_apply (m₁ m₂ : PFun α β) (a : α) :
    (m₁ ∪ m₂) a = if (m₁ a).Dom then m₁ a else m₂ a := rfl

@[simp] theorem insert_apply [DecidableEq α] (a : α) (b : β) (m : PFun α β) (a' : α) :
    insert a b m a' = if a' = a then Part.some b else m a' := rfl

@[simp] theorem mem_dom {m : PFun α β} {a : α} : a ∈ dom m ↔ ∃ b, m a = Part.some b := by
  simp only [dom, Set.mem_setOf_eq, Part.dom_iff_mem]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, Part.eq_some_iff.2 hb⟩, fun ⟨b, hb⟩ => ⟨b, Part.eq_some_iff.1 hb⟩⟩

@[simp] theorem not_mem_dom {m : PFun α β} {a : α} : a ∉ dom m ↔ m a = Part.none := by
  simp only [dom, Set.mem_setOf_eq, Part.eq_none_iff']

theorem union_apply_eq_some {m₁ m₂ : PFun α β} {a : α} {b : β} :
    (m₁ ∪ m₂) a = Part.some b ↔ m₁ a = Part.some b ∨ (m₁ a = Part.none ∧ m₂ a = Part.some b) := by
  rw [union_apply]
  by_cases h : (m₁ a).Dom
  · have hne : ¬ (m₁ a = Part.none) := by rw [Part.eq_none_iff']; simpa using h
    simp only [h, if_true]; tauto
  · have hnone : m₁ a = Part.none := Part.eq_none_iff'.2 h
    simp [hnone]

theorem union_apply_some_l {m₁ m₂ : PFun α β} {a : α} {b : β} (h : m₁ a = Part.some b) :
    (m₁ ∪ m₂) a = Part.some b := union_apply_eq_some.2 (Or.inl h)

theorem insert_apply_ne [DecidableEq α] {a a' : α} (b : β) (m : PFun α β) (h : a' ≠ a) :
    insert a b m a' = m a' := by simp [insert_apply, h]

/-! ### Disjointness -/

theorem Disjoint.symm {m₁ m₂ : PFun α β} (h : m₁ ##ₘ m₂) : m₂ ##ₘ m₁ := fun a => (h a).symm

theorem Disjoint.some_l {m₁ m₂ : PFun α β} {a : α} {b : β}
    (h : m₁ ##ₘ m₂) (ha : m₁ a = Part.some b) : m₂ a = Part.none := by
  rcases h a with h' | h'
  · rw [h'] at ha; exact absurd ha (by simp)
  · exact h'

@[simp] theorem disjoint_empty_l (m : PFun α β) : (∅ : PFun α β) ##ₘ m := fun _ => Or.inl rfl
@[simp] theorem disjoint_empty_r (m : PFun α β) : m ##ₘ (∅ : PFun α β) := fun _ => Or.inr rfl

@[simp] theorem disjoint_insert_l [DecidableEq α] {m₁ m₂ : PFun α β} {a : α} {b : β} :
    insert a b m₁ ##ₘ m₂ ↔ m₂ a = Part.none ∧ m₁ ##ₘ m₂ := by
  constructor
  · intro h
    refine ⟨?_, fun a' => ?_⟩
    · rcases h a with h' | h'
      · simp [insert_apply] at h'
      · exact h'
    · by_cases ha' : a' = a
      · subst ha'; right; rcases h a' with h' | h' <;> simp_all [insert_apply]
      · rcases h a' with h' | h'
        · left; rwa [insert_apply_ne _ _ ha'] at h'
        · right; exact h'
  · rintro ⟨h₁, h₂⟩ a'
    by_cases ha' : a' = a
    · subst ha'; right; exact h₁
    · rcases h₂ a' with h' | h'
      · left; rwa [insert_apply_ne _ _ ha']
      · right; exact h'

@[simp] theorem disjoint_union_l {m₁ m₂ m₃ : PFun α β} :
    m₁ ∪ m₂ ##ₘ m₃ ↔ (m₁ ##ₘ m₃) ∧ (m₂ ##ₘ m₃) := by
  constructor
  · intro h
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rcases h a with h' | h'
      · rw [union_apply] at h'
        by_cases hd : (m₁ a).Dom
        · rw [if_pos hd] at h'; exact Or.inl h'
        · exact Or.inl (Part.eq_none_iff'.2 hd)
      · exact Or.inr h'
    · rcases h a with h' | h'
      · rw [union_apply] at h'
        by_cases hd : (m₁ a).Dom
        · exact absurd hd (Part.eq_none_iff'.1 (by rw [if_pos hd] at h'; exact h'))
        · rw [if_neg hd] at h'; exact Or.inl h'
      · exact Or.inr h'
  · rintro ⟨h₁, h₂⟩ a
    rcases h₁ a with h' | h'
    · rcases h₂ a with h'' | h''
      · left; rw [union_apply, if_neg (h' ▸ Part.not_none_dom), h'']
      · right; exact h''
    · right; exact h'

@[simp] theorem disjoint_union_r {m₁ m₂ m₃ : PFun α β} :
    m₁ ##ₘ m₂ ∪ m₃ ↔ (m₁ ##ₘ m₂) ∧ (m₁ ##ₘ m₃) := by
  constructor
  · intro h
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rcases h a with h' | h'
      · exact Or.inl h'
      · rw [union_apply] at h'
        by_cases hd : (m₂ a).Dom
        · exact absurd hd (Part.eq_none_iff'.1 (by rw [if_pos hd] at h'; exact h'))
        · exact Or.inr (Part.eq_none_iff'.2 hd)
    · rcases h a with h' | h'
      · exact Or.inl h'
      · rw [union_apply] at h'
        by_cases hd : (m₂ a).Dom
        · exact absurd hd (Part.eq_none_iff'.1 (by rw [if_pos hd] at h'; exact h'))
        · rw [if_neg hd] at h'; exact Or.inr h'
  · rintro ⟨h₁, h₂⟩ a
    rcases h₁ a with h' | h'
    · exact Or.inl h'
    · rcases h₂ a with h'' | h''
      · exact Or.inl h''
      · right; rw [union_apply, if_neg (h' ▸ Part.not_none_dom), h'']

theorem disjoint_some_insert [DecidableEq α] {m₁ m₂ : PFun α β} {a : α} {x : β} (y : β)
    (h : m₁ a = Part.some x) (hdisj : m₁ ##ₘ m₂) : insert a y m₁ ##ₘ m₂ := by
  rw [disjoint_insert_l]
  exact ⟨hdisj.some_l h, hdisj⟩

/-! ### Union -/

@[simp] theorem empty_union (m : PFun α β) : ∅ ∪ m = m := by
  ext a; simp [union_apply, Part.not_none_dom]

@[simp] theorem union_empty (m : PFun α β) : m ∪ ∅ = m := by
  apply ext; intro a; rw [union_apply]
  by_cases h : (m a).Dom
  · simp [h]
  · simp only [h, if_false, empty_apply]; exact (Part.eq_none_iff'.2 h).symm

theorem union_assoc (m₁ m₂ m₃ : PFun α β) : m₁ ∪ m₂ ∪ m₃ = m₁ ∪ (m₂ ∪ m₃) := by
  ext a; simp only [union_apply]
  by_cases h1 : (m₁ a).Dom <;> simp [h1]

theorem union_comm {m₁ m₂ : PFun α β} (h : m₁ ##ₘ m₂) : m₁ ∪ m₂ = m₂ ∪ m₁ := by
  ext a; simp only [union_apply]
  rcases h a with h' | h'
  · rw [if_neg (h' ▸ Part.not_none_dom)]
    by_cases hd2 : (m₂ a).Dom
    · rw [if_pos hd2]
    · rw [if_neg hd2, h', Part.eq_none_iff'.2 hd2]
  · rw [if_neg (show ¬(m₂ a).Dom from h' ▸ Part.not_none_dom)]
    by_cases hd1 : (m₁ a).Dom
    · rw [if_pos hd1]
    · rw [if_neg hd1, h', Part.eq_none_iff'.2 hd1]

theorem union_id_l (m : PFun α β) : m = ∅ ∪ m := by simp

theorem insert_union_l [DecidableEq α] (a : α) (b : β) (m₁ m₂ : PFun α β) :
    insert a b m₁ ∪ m₂ = insert a b (m₁ ∪ m₂) := by
  ext a'; simp only [union_apply, insert_apply]
  by_cases h : a' = a <;> simp [h]

/-! ### Domain -/

@[simp] theorem dom_union (m₁ m₂ : PFun α β) : dom (m₁ ∪ m₂) = dom m₁ ∪ dom m₂ := by
  ext a; simp only [mem_dom, Set.mem_union, union_apply_eq_some]
  constructor
  · rintro ⟨b, hb | ⟨_, hb⟩⟩
    · exact Or.inl ⟨b, hb⟩
    · exact Or.inr ⟨b, hb⟩
  · rintro (⟨b, hb⟩ | ⟨b, hb⟩)
    · exact ⟨b, Or.inl hb⟩
    · by_cases hd : m₁ a = Part.none
      · exact ⟨b, Or.inr ⟨hd, hb⟩⟩
      · obtain ⟨b', hb'⟩ := Part.dom_iff_mem.1 (by rwa [Part.eq_none_iff', not_not] at hd)
        exact ⟨b', Or.inl (Part.eq_some_iff.2 hb')⟩

@[simp] theorem dom_empty : dom (∅ : PFun α β) = ∅ := by
  ext a; simp only [dom, empty_apply, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact Part.not_none_dom

@[simp] theorem dom_insert [DecidableEq α] (a : α) (b : β) (m : PFun α β) :
    dom (insert a b m) = {a} ∪ dom m := by
  ext a'
  by_cases h : a' = a
  · subst h; simp [dom, insert_apply]
  · simp [dom, insert_apply, h]

/-! ### Inclusion -/

theorem empty_subset (m : PFun α β) : (∅ : PFun α β) ⊆ m := fun _ _ h => by simp at h

theorem subset_apply {m₁ m₂ : PFun α β} (h : m₁ ⊆ m₂) {a : α} {b : β}
    (ha : m₁ a = Part.some b) : m₂ a = Part.some b := h a b ha

theorem insert_mono [DecidableEq α] {m₁ m₂ : PFun α β} (a : α) (b : β) (h : m₁ ⊆ m₂) :
    insert a b m₁ ⊆ insert a b m₂ := by
  intro a' b' hb'
  simp only [insert_apply] at hb' ⊢
  by_cases ha' : a' = a
  · simpa [ha'] using hb'
  · simp only [ha', if_false] at hb' ⊢; exact h a' b' hb'

theorem insert_comm [DecidableEq α] {a a' : α} (h : a ≠ a') (b b' : β) (m : PFun α β) :
    insert a b (insert a' b' m) = insert a' b' (insert a b m) := by
  ext a''; simp only [insert_apply]
  by_cases h1 : a'' = a <;> by_cases h2 : a'' = a' <;> simp_all

end PFun

end RUXt
