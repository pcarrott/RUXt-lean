/-
Port of `theories/lang/assertion.v`: logical assertions on heaps.
-/
import RUXt.Lang.Semantics

namespace RUXt

open scoped RUXt.PMap

universe u

/-! ### Assertion language -/

/-- Assertions (`asrt`). Lives in `Type 1` because `ex` quantifies over
arbitrary (small) types. -/
inductive Asrt : Type 1
  | pure (P : Prop)
  | true
  | false
  | and (a₁ a₂ : Asrt)
  | or (a₁ a₂ : Asrt)
  | implies (a₁ a₂ : Asrt)
  | ex {X : Type} (P : X → Asrt)
  | emp
  | single (l : Loc) (bv : BlockValue)
  | star (a₁ a₂ : Asrt)

/-- `⌞ P ⌟`: a pure assertion over the empty heap. -/
scoped notation "⌞" P "⌟" => Asrt.pure P

/-- Conjunction of assertions (`P ∧ₕ Q`). -/
scoped infixr:62 " ∧ₕ " => Asrt.and
/-- Disjunction of assertions (`P ∨ₕ Q`). -/
scoped infixr:61 " ∨ₕ " => Asrt.or
/-- Implication of assertions (`P →ₕ Q`). -/
scoped infixr:60 " →ₕ " => Asrt.implies
/-- Separating conjunction (`P ∗ Q`). -/
scoped infixr:63 " ∗ " => Asrt.star

/-- `l ↦ v`: the heap is a single one-cell block at `l` containing `v`. -/
def Asrt.pointsTo (l : Loc) (v : Val) : Asrt :=
  .single l (.block 1 (PMap.singleton l.2 (.val v)))

/-- `l ↦∅`: the heap is a single freed block at `l`. -/
def Asrt.pointsToFreed (l : Loc) : Asrt := .single l .freed

/-- `l ↦?`: the heap is a single uninitialised one-cell block at `l`. -/
def Asrt.pointsToUninit (l : Loc) : Asrt :=
  .single l (.block 1 (PMap.singleton l.2 .poison))

@[inherit_doc] scoped infix:67 " ↦ " => Asrt.pointsTo
@[inherit_doc] scoped postfix:67 " ↦∅" => Asrt.pointsToFreed
@[inherit_doc] scoped postfix:67 " ↦?" => Asrt.pointsToUninit

/-- `⌜ P ⌝`: `P` weakened to an affine assertion (notation for `P ∗ TRUE`,
exactly as in the Rocq development). -/
scoped notation "⌜" P "⌝" => Asrt.star P Asrt.true

/-- `AIterL`: iterated separating conjunction over a list, with access to the
position of each element. -/
def Asrt.iterL {X : Type u} (xs : List X) (P : ℕ → X → Asrt) : Asrt :=
  match xs with
  | [] => .emp
  | x :: xs => P 0 x ∗ Asrt.iterL xs (fun n => P (n + 1))

/-- `[∗ xs , P]`: iterated separating conjunction over a list. -/
def Asrt.iter {X : Type u} (xs : List X) (P : X → Asrt) : Asrt :=
  Asrt.iterL xs fun _ => P

@[simp] theorem Asrt.iter_nil {X : Type u} (P : X → Asrt) :
    Asrt.iter ([] : List X) P = .emp := rfl

@[simp] theorem Asrt.iter_cons {X : Type u} (P : X → Asrt) (x : X) (xs : List X) :
    Asrt.iter (x :: xs) P = P x ∗ Asrt.iter xs P := rfl

/-- `l ↦∗ vs`: `vs` stored contiguously starting at `l`. -/
def Asrt.pointsToMany (l : Loc) (vs : List Val) : Asrt :=
  .iterL vs fun i v => (l +ₗ i) ↦ v

/-- `opt_init`: an optionally initialised cell. -/
def optInit (l : Loc) (v : Option Val) : Asrt :=
  match v with
  | some v => l ↦ v
  | none => Asrt.pointsToUninit l

/-- `l ↦∗? vs`: optionally initialised cells stored contiguously at `l`. -/
def Asrt.pointsToManyOpt (l : Loc) (vs : List (Option Val)) : Asrt :=
  .iterL vs fun i v => optInit (l +ₗ i) v

/-! ### Assertion semantics -/

/-- `hprop`: satisfaction of an assertion by a heap. -/
def hprop (h : Heap) : Asrt → Prop
  | ⌞P⌟ => h = ∅ ∧ P
  | .true => True
  | .false => False
  | .and a₁ a₂ => hprop h a₁ ∧ hprop h a₂
  | .or a₁ a₂ => hprop h a₁ ∨ hprop h a₂
  | .implies a₁ a₂ => hprop h a₁ → hprop h a₂
  | .ex P => ∃ x, hprop h (P x)
  | .emp => h = ∅
  | .single l bv => h = PMap.singleton l.1 bv ∧ l.2 = 0
  | a₁ ∗ a₂ => ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ hprop h₁ a₁ ∧ hprop h₂ a₂

section hprop_simp

variable {h : Heap}

@[simp] theorem hprop_pure {P : Prop} : hprop h ⌞P⌟ ↔ h = ∅ ∧ P := Iff.rfl
@[simp] theorem hprop_true : hprop h .true ↔ True := Iff.rfl
@[simp] theorem hprop_false : hprop h .false ↔ False := Iff.rfl
@[simp] theorem hprop_and {a₁ a₂ : Asrt} :
    hprop h (a₁ ∧ₕ a₂) ↔ hprop h a₁ ∧ hprop h a₂ := Iff.rfl
@[simp] theorem hprop_or {a₁ a₂ : Asrt} :
    hprop h (a₁ ∨ₕ a₂) ↔ hprop h a₁ ∨ hprop h a₂ := Iff.rfl
@[simp] theorem hprop_implies {a₁ a₂ : Asrt} :
    hprop h (a₁ →ₕ a₂) ↔ (hprop h a₁ → hprop h a₂) := Iff.rfl
@[simp] theorem hprop_ex {X : Type} {P : X → Asrt} :
    hprop h (.ex P) ↔ ∃ x, hprop h (P x) := Iff.rfl
@[simp] theorem hprop_emp : hprop h .emp ↔ h = ∅ := Iff.rfl
@[simp] theorem hprop_single {l : Loc} {bv : BlockValue} :
    hprop h (.single l bv) ↔ h = PMap.singleton l.1 bv ∧ l.2 = 0 := Iff.rfl
@[simp] theorem hprop_star {a₁ a₂ : Asrt} :
    hprop h (a₁ ∗ a₂) ↔
    ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ hprop h₁ a₁ ∧ hprop h₂ a₂ := Iff.rfl

@[simp] theorem hprop_pointsTo {l : Loc} {v : Val} :
    hprop h (l ↦ v) ↔
    h = PMap.singleton l.1 (.block 1 (PMap.singleton l.2 (.val v))) ∧ l.2 = 0 := Iff.rfl

@[simp] theorem hprop_pointsToFreed {l : Loc} :
    hprop h (l ↦∅) ↔ h = PMap.singleton l.1 .freed ∧ l.2 = 0 := Iff.rfl

@[simp] theorem hprop_pointsToUninit {l : Loc} :
    hprop h (l ↦?) ↔
    h = PMap.singleton l.1 (.block 1 (PMap.singleton l.2 .poison)) ∧ l.2 = 0 := Iff.rfl

end hprop_simp

/-- `hmodels` (`P ⊨ Q`): every heap satisfying `P` has a subheap satisfying `Q`. -/
def hmodels (P Q : Asrt) : Prop :=
  ∀ h, hprop h P → ∃ h', h' ⊆ h ∧ hprop h' Q

@[inherit_doc] scoped infix:24 " ⊨ " => hmodels

/-- `hvalid` (`⊨ P`): `P` holds of every heap. -/
def hvalid (P : Asrt) : Prop := ∀ h, hprop h P

@[inherit_doc] scoped prefix:24 "⊨ " => hvalid

/-- `sat`: satisfiability. -/
def sat (P : Asrt) : Prop := ∃ h, hprop h P

/-! ### Properties: separating conjunction -/

/-- `hstar_comm`. -/
theorem hstar_comm {P Q : Asrt} {h : Heap} : hprop h (P ∗ Q) ↔ hprop h (Q ∗ P) := by
  constructor <;>
    · rintro ⟨h₁, h₂, rfl, hdisj, hP, hQ⟩
      exact ⟨h₂, h₁, PMap.union_comm hdisj, hdisj.symm, hQ, hP⟩

/-- `hstar_assoc`. -/
theorem hstar_assoc {P Q R : Asrt} {h : Heap} :
    hprop h ((P ∗ Q) ∗ R) ↔ hprop h (P ∗ (Q ∗ R)) := by
  constructor
  · rintro ⟨h₁₂, h₃, rfl, hdisj, ⟨h₁, h₂, rfl, hdisj₁₂, hP, hQ⟩, hR⟩
    rw [PMap.disjoint_union_l] at hdisj
    exact ⟨h₁, h₂ ∪ h₃, PMap.union_assoc .., by simp [hdisj₁₂, hdisj.1],
      hP, h₂, h₃, rfl, hdisj.2, hQ, hR⟩
  · rintro ⟨h₁, h₂₃, rfl, hdisj, hP, h₂, h₃, rfl, hdisj₂₃, hQ, hR⟩
    rw [PMap.disjoint_union_r] at hdisj
    exact ⟨h₁ ∪ h₂, h₃, (PMap.union_assoc ..).symm, by simp [hdisj₂₃, hdisj.2],
      ⟨h₁, h₂, rfl, hdisj.1, hP, hQ⟩, hR⟩

/-- A congruence helper for rewriting under the right-hand side of `∗`
(in Rocq this is `rewrite` of an `↔` in place, which Lean lacks). -/
theorem hprop_star_congr_r {P Q Q' : Asrt}
    (hQ : ∀ h, hprop h Q ↔ hprop h Q') {h : Heap} :
    hprop h (P ∗ Q) ↔ hprop h (P ∗ Q') := by
  constructor <;>
    · rintro ⟨h₁, h₂, rfl, hdisj, hP, hq⟩
      exact ⟨h₁, h₂, rfl, hdisj, hP, by rw [hQ h₂] at *; exact hq⟩

/-- `hstar_sat`. -/
theorem hstar_sat {P Q : Asrt} (h : sat (P ∗ Q)) : sat P ∧ sat Q := by
  obtain ⟨h, h₁, h₂, rfl, hdisj, hP, hQ⟩ := h
  exact ⟨⟨h₁, hP⟩, ⟨h₂, hQ⟩⟩

/-! ### Properties: iterated star -/

/-- `hiter_nil`. -/
theorem hiter_nil {X : Type u} (P : X → Asrt) (h : Heap) :
    hprop h (Asrt.iter ([] : List X) P) ↔ hprop h .emp := Iff.rfl

/-- `hiter_cons`. -/
theorem hiter_cons {X : Type u} (P : X → Asrt) (x : X) (xs : List X) (h : Heap) :
    hprop h (Asrt.iter (x :: xs) P) ↔ hprop h (P x ∗ Asrt.iter xs P) := Iff.rfl

/-- `hiter_singleton`. -/
theorem hiter_singleton {X : Type u} (P : X → Asrt) (x : X) (h : Heap) :
    hprop h (Asrt.iter [x] P) ↔ hprop h (P x) := by
  constructor
  · rintro ⟨h₁, h₂, rfl, hdisj, hP, (rfl : h₂ = ∅)⟩
    simpa using hP
  · intro hP
    exact ⟨h, ∅, (PMap.union_empty h).symm, PMap.disjoint_empty_r h, hP, rfl⟩

/-- `hiter_app`. -/
theorem hiter_app {X : Type u} (P : X → Asrt) (xs ys : List X) (h : Heap) :
    hprop h (Asrt.iter (xs ++ ys) P) ↔ hprop h (Asrt.iter xs P ∗ Asrt.iter ys P) := by
  induction xs generalizing h with
  | nil =>
    simp only [List.nil_append, Asrt.iter_nil]
    constructor
    · intro hys
      exact ⟨∅, h, (PMap.empty_union h).symm, PMap.disjoint_empty_l h, rfl, hys⟩
    · rintro ⟨h₁, h₂, rfl, hdisj, (rfl : h₁ = ∅), hys⟩
      simpa using hys
  | cons a xs ih =>
    simp only [List.cons_append, Asrt.iter_cons]
    exact (hprop_star_congr_r fun h => ih h).trans hstar_assoc.symm

/-- `hiter_permutation`. -/
theorem hiter_perm {X : Type u} (P : X → Asrt) {xs ys : List X} (h : Heap)
    (hperm : xs.Perm ys) :
    hprop h (Asrt.iter xs P) ↔ hprop h (Asrt.iter ys P) := by
  induction hperm generalizing h with
  | nil => exact Iff.rfl
  | cons a _ ih => exact hprop_star_congr_r fun h => ih h
  | swap a b l =>
    simp only [Asrt.iter_cons]
    constructor <;>
      · rintro ⟨h₁, h₂, rfl, hdisj, hPb, h₃, h₄, rfl, hdisj₂, hPa, hR⟩
        rw [PMap.disjoint_union_r] at hdisj
        refine ⟨h₃, h₁ ∪ h₄, ?_, ?_, hPa, h₁, h₄, rfl, hdisj.2, hPb, hR⟩
        · rw [← PMap.union_assoc, PMap.union_comm hdisj.1, PMap.union_assoc]
        · simp [hdisj.1.symm, hdisj₂]
  | trans _ _ ih₁ ih₂ => exact (ih₁ h).trans (ih₂ h)

/-- `hiter_submseteq`. -/
theorem hiter_subperm {X : Type u} (P : X → Asrt) {xs ys : List X} {h : Heap}
    (hsub : ys.Subperm xs) (hiter : hprop h (Asrt.iter xs P)) :
    ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ hprop h₁ (Asrt.iter ys P) := by
  obtain ⟨l, hl_perm, hl_sub⟩ := hsub
  obtain ⟨zs, hperm⟩ := hl_sub.exists_perm_append
  rw [hiter_perm P h (hperm.trans (hl_perm.append_right zs)), hiter_app] at hiter
  obtain ⟨h₁, h₂, rfl, hdisj, hys, _⟩ := hiter
  exact ⟨h₁, h₂, rfl, hdisj, hys⟩

/-- `elem_of_hiter`. -/
theorem elem_of_hiter {X : Type u} (P : X → Asrt) {x : X} {xs : List X} {h : Heap}
    (hin : x ∈ xs) (hiter : hprop h (Asrt.iter xs P)) :
    ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ hprop h₁ (P x) := by
  obtain ⟨h₁, h₂, rfl, hdisj, hx⟩ :=
    hiter_subperm P (List.singleton_subperm_iff.mpr hin) hiter
  exact ⟨h₁, h₂, rfl, hdisj, (hiter_singleton P x h₁).mp hx⟩

/-! ### Properties: weakening -/

/-- `hpure_weaken`. -/
theorem hpure_weaken (P : Asrt) (Q : Prop) (h : Heap) : hprop h (P ∗ ⌞Q⌟ →ₕ P) := by
  rintro ⟨h₁, h₂, rfl, hdisj, hP, rfl, _⟩
  simpa using hP

/-- `htrue_weaken`. -/
theorem htrue_weaken (P : Asrt) (h : Heap) : hprop h (.true ∗ P →ₕ .true) :=
  fun _ => trivial

/-- `haffine_weaken`. -/
theorem haffine_weaken (P Q : Asrt) (h : Heap) : hprop h (⌜P⌝ ∗ Q →ₕ ⌜P⌝) := by
  intro hstar
  rw [show hprop h ((P ∗ .true) ∗ Q) ↔ hprop h (P ∗ (.true ∗ Q)) from hstar_assoc]
    at hstar
  obtain ⟨h₁, h₂, rfl, hdisj, hP, _⟩ := hstar
  exact ⟨h₁, h₂, rfl, hdisj, hP, trivial⟩

/-! ### Properties: implication -/

/-- `himplies_refl`. -/
theorem himplies_refl (P : Asrt) : ⊨ (P →ₕ P) :=
  fun _ hP => hP

/-- `hempty_left`. -/
theorem hempty_left (P : Asrt) : ⊨ (P ∗ .emp →ₕ P) := by
  rintro h ⟨h₁, h₂, rfl, hdisj, hP, (rfl : h₂ = ∅)⟩
  simpa using hP

/-- `hempty_right`. -/
theorem hempty_right (P : Asrt) : ⊨ (P →ₕ P ∗ .emp) :=
  fun h hP => ⟨h, ∅, (PMap.union_empty h).symm, PMap.disjoint_empty_r h, hP, rfl⟩

end RUXt
