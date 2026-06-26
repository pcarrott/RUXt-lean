import RUXt.Lang.Semantics
import Mathlib.Data.List.Perm.Basic

namespace RUXt

open scoped PFun

universe u

/-! ### Assertion language -/

/-- Assertions. Lives in `Type (u + 1)` because existentials
quantify over arbitrary smaller types in `Type u`. -/
inductive Asrt : Type (u + 1)
  | pure (P : Prop)
  | true
  | false
  | and (a₁ a₂ : Asrt)
  | or (a₁ a₂ : Asrt)
  | implies (a₁ a₂ : Asrt)
  | ex {X : Type u} (P : X → Asrt)
  | emp
  | single (l : Loc) (bv : BlockValue)
  | star (a₁ a₂ : Asrt)

/-- `⌞ P ⌟`: a pure assertion over the empty heap. -/
scoped notation "⌞" P "⌟" => Asrt.pure P
/-- `⌜ P ⌝`: `P` weakened to an affine assertion (notation for `P ∗ TRUE`,
exactly as in the Rocq development). -/
scoped notation "⌜" P "⌝" => Asrt.star P Asrt.true

/-- `l ↦ v`: the heap is a single one-cell block at `l` containing `v`. -/
def Asrt.pointsTo (l : Loc) (v : Val) : Asrt :=
  .single l (.block 1 (PFun.singleton l.2 (.val v)))
@[inherit_doc] scoped infix:67 " ↦ " => Asrt.pointsTo
/-- `l ↦∅`: the heap is a single freed block at `l`. -/
def Asrt.pointsToFreed (l : Loc) : Asrt :=
  .single l .freed
@[inherit_doc] scoped postfix:67 " ↦∅" => Asrt.pointsToFreed
/-- `l ↦?`: the heap is a single uninitialised one-cell block at `l`. -/
def Asrt.pointsToUninit (l : Loc) : Asrt :=
  .single l (.block 1 (PFun.singleton l.2 .poison))
@[inherit_doc] scoped postfix:67 " ↦?" => Asrt.pointsToUninit

/-- `P ∧ₕ Q`: conjunction of assertions. -/
scoped infixr:62 " ∧ₕ " => Asrt.and
/-- `P ∨ₕ Q`: disjunction of assertions. -/
scoped infixr:61 " ∨ₕ " => Asrt.or
/-- `P →ₕ Q`: implication of assertions. -/
scoped infixr:60 " →ₕ " => Asrt.implies
/-- `P ∗ Q`: separating conjunction. -/
scoped infixr:63 " ∗ " => Asrt.star

/-- `AIterL`: iterated separating conjunction over a list, with access to the
position of each element. -/
def Asrt.iterI {X : Type u} (xs : List X) (P : ℕ → X → Asrt) : Asrt :=
  match xs with
  | [] => .emp
  | x :: xs => P 0 x ∗ Asrt.iterI xs (fun n => P (n + 1))
/-- `[∗ xs , P]`: iterated separating conjunction over a list. -/
def Asrt.iter {X : Type u} (xs : List X) (P : X → Asrt) : Asrt :=
  Asrt.iterI xs fun _ => P

@[simp] theorem Asrt.iter_nil {X : Type u} (P : X → Asrt) :
    Asrt.iter ([] : List X) P = .emp := rfl
@[simp] theorem Asrt.iter_cons {X : Type u} (P : X → Asrt) (x : X) (xs : List X) :
    Asrt.iter (x :: xs) P = P x ∗ Asrt.iter xs P := rfl

/-- `l ↦∗ vs`: `vs` stored contiguously starting at `l`. -/
def Asrt.pointsToMany (l : Loc) (vs : List Val) : Asrt :=
  .iterI vs fun i v => (l +ₗ i) ↦ v
/-- `opt_init`: an optionally initialised cell. -/
def optInit (l : Loc) (v : Option Val) : Asrt :=
  match v with
  | some v => l ↦ v
  | none => Asrt.pointsToUninit l
/-- `l ↦∗? vs`: optionally initialised cells stored contiguously at `l`. -/
def Asrt.pointsToManyOpt (l : Loc) (vs : List (Option Val)) : Asrt :=
  .iterI vs fun i v => optInit (l +ₗ i) v

/-! ### Assertion semantics -/

/-- `HProp`: satisfaction of an assertion by a heap. -/
def HProp (h : Heap) : Asrt → Prop
  | .pure P => h = ∅ ∧ P
  | .true => True
  | .false => False
  | .and a₁ a₂ => HProp h a₁ ∧ HProp h a₂
  | .or a₁ a₂ => HProp h a₁ ∨ HProp h a₂
  | .implies a₁ a₂ => HProp h a₁ → HProp h a₂
  | .ex P => ∃ x, HProp h (P x)
  | .emp => h = ∅
  | .single ⟨b, i⟩ bv => h = PFun.singleton b bv ∧ i = 0
  | .star a₁ a₂ => ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ HProp h₁ a₁ ∧ HProp h₂ a₂

/-- `HModels` (`P ⊨ Q`): every heap satisfying `P` has a subheap satisfying `Q`. -/
def HModels (P Q : Asrt) : Prop :=
  ∀ h, HProp h P → ∃ h', h' ⊆ h ∧ HProp h' Q
@[inherit_doc] scoped infix:24 " ⊨ " => HModels
/-- `HValid` (`⊨ P`): `P` holds of every heap. -/
def HValid (P : Asrt) : Prop := ∀ h, HProp h P
@[inherit_doc] scoped prefix:24 "⊨ " => HValid
/-- `Sat`: satisfiability. -/
def Sat (P : Asrt) : Prop := ∃ h, HProp h P

section hProp_simp

variable {h : Heap}

@[simp] theorem hProp_pure {P : Prop} : HProp h ⌞P⌟ ↔ h = ∅ ∧ P := Iff.rfl
@[simp] theorem hProp_true : HProp h .true ↔ True := Iff.rfl
@[simp] theorem hProp_false : HProp h .false ↔ False := Iff.rfl
@[simp] theorem hProp_and {a₁ a₂ : Asrt} :
    HProp h (a₁ ∧ₕ a₂) ↔ HProp h a₁ ∧ HProp h a₂ := Iff.rfl
@[simp] theorem hProp_or {a₁ a₂ : Asrt} :
    HProp h (a₁ ∨ₕ a₂) ↔ HProp h a₁ ∨ HProp h a₂ := Iff.rfl
@[simp] theorem hProp_implies {a₁ a₂ : Asrt} :
    HProp h (a₁ →ₕ a₂) ↔ (HProp h a₁ → HProp h a₂) := Iff.rfl
@[simp] theorem hProp_ex {X : Type} {P : X → Asrt} :
    HProp h (.ex P) ↔ ∃ x, HProp h (P x) := Iff.rfl
@[simp] theorem hProp_emp : HProp h .emp ↔ h = ∅ := Iff.rfl
@[simp] theorem hProp_single {l : Loc} {bv : BlockValue} :
    HProp h (.single l bv) ↔ h = PFun.singleton l.1 bv ∧ l.2 = 0 := Iff.rfl
@[simp] theorem hProp_star {a₁ a₂ : Asrt} :
    HProp h (a₁ ∗ a₂) ↔
    ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ HProp h₁ a₁ ∧ HProp h₂ a₂ := Iff.rfl
@[simp] theorem hProp_pointsTo {l : Loc} {v : Val} :
    HProp h (l ↦ v) ↔
    h = PFun.singleton l.1 (.block 1 (PFun.singleton l.2 (.val v))) ∧ l.2 = 0 := Iff.rfl
@[simp] theorem hProp_pointsToFreed {l : Loc} :
    HProp h (l ↦∅) ↔ h = PFun.singleton l.1 .freed ∧ l.2 = 0 := Iff.rfl
@[simp] theorem hProp_pointsToUninit {l : Loc} :
    HProp h (l ↦?) ↔
    h = PFun.singleton l.1 (.block 1 (PFun.singleton l.2 .poison)) ∧ l.2 = 0 := Iff.rfl

end hProp_simp

/-! ### Properties: separating conjunction -/

theorem hStar_comm {P Q : Asrt} {h : Heap} : HProp h (P ∗ Q) ↔ HProp h (Q ∗ P) := by
  constructor <;>
    · rintro ⟨h₁, h₂, rfl, hdisj, hP, hQ⟩
      exact ⟨h₂, h₁, PFun.union_comm hdisj, hdisj.symm, hQ, hP⟩

theorem hStar_assoc {P Q R : Asrt} {h : Heap} :
    HProp h ((P ∗ Q) ∗ R) ↔ HProp h (P ∗ (Q ∗ R)) := by
  constructor
  · rintro ⟨h₁₂, h₃, rfl, hdisj, ⟨h₁, h₂, rfl, hdisj₁₂, hP, hQ⟩, hR⟩
    rw [PFun.disjoint_union_l] at hdisj
    exact ⟨h₁, h₂ ∪ h₃, PFun.union_assoc .., by simp [hdisj₁₂, hdisj.1],
      hP, h₂, h₃, rfl, hdisj.2, hQ, hR⟩
  · rintro ⟨h₁, h₂₃, rfl, hdisj, hP, h₂, h₃, rfl, hdisj₂₃, hQ, hR⟩
    rw [PFun.disjoint_union_r] at hdisj
    exact ⟨h₁ ∪ h₂, h₃, (PFun.union_assoc ..).symm, by simp [hdisj₂₃, hdisj.2],
      ⟨h₁, h₂, rfl, hdisj.1, hP, hQ⟩, hR⟩

theorem hStar_sat {P Q : Asrt} (h : Sat (P ∗ Q)) : Sat P ∧ Sat Q := by
  obtain ⟨h, h₁, h₂, rfl, hdisj, hP, hQ⟩ := h
  exact ⟨⟨h₁, hP⟩, ⟨h₂, hQ⟩⟩

/-- A congruence helper for rewriting under the right-hand side of `∗`
(in Rocq this is `rewrite` of an `↔` in place, which Lean lacks). -/
theorem hStar_congr_r {P Q Q' : Asrt}
    (hQ : ∀ h, HProp h Q ↔ HProp h Q') {h : Heap} :
    HProp h (P ∗ Q) ↔ HProp h (P ∗ Q') := by
  constructor <;>
    · rintro ⟨h₁, h₂, rfl, hdisj, hP, hq⟩
      exact ⟨h₁, h₂, rfl, hdisj, hP, by rw [hQ h₂] at *; exact hq⟩

/-! ### Properties: iterated star -/

theorem hIter_nil {X : Type u} (P : X → Asrt) (h : Heap) :
    HProp h (Asrt.iter ([] : List X) P) ↔ HProp h .emp := Iff.rfl

theorem hIter_cons {X : Type u} (P : X → Asrt) (x : X) (xs : List X) (h : Heap) :
    HProp h (Asrt.iter (x :: xs) P) ↔ HProp h (P x ∗ Asrt.iter xs P) := Iff.rfl

theorem hIter_singleton {X : Type u} (P : X → Asrt) (x : X) (h : Heap) :
    HProp h (Asrt.iter [x] P) ↔ HProp h (P x) := by
  constructor
  · rintro ⟨h₁, h₂, rfl, hdisj, hP, (rfl : h₂ = ∅)⟩
    simpa using hP
  · intro hP
    exact ⟨h, ∅, (PFun.union_empty h).symm, PFun.disjoint_empty_r h, hP, rfl⟩

theorem hIter_app {X : Type u} (P : X → Asrt) (xs ys : List X) (h : Heap) :
    HProp h (Asrt.iter (xs ++ ys) P) ↔ HProp h (Asrt.iter xs P ∗ Asrt.iter ys P) := by
  induction xs generalizing h with
  | nil =>
    simp only [List.nil_append, Asrt.iter_nil]
    constructor
    · intro hys
      exact ⟨∅, h, (PFun.empty_union h).symm, PFun.disjoint_empty_l h, rfl, hys⟩
    · rintro ⟨h₁, h₂, rfl, hdisj, (rfl : h₁ = ∅), hys⟩
      simpa using hys
  | cons a xs ih =>
    simp only [List.cons_append, Asrt.iter_cons]
    exact (hStar_congr_r fun h => ih h).trans hStar_assoc.symm

theorem hIter_perm {X : Type u} (P : X → Asrt) {xs ys : List X} (h : Heap)
    (hperm : xs.Perm ys) :
    HProp h (Asrt.iter xs P) ↔ HProp h (Asrt.iter ys P) := by
  induction hperm generalizing h with
  | nil => exact Iff.rfl
  | cons a _ ih => exact hStar_congr_r fun h => ih h
  | swap a b l =>
    simp only [Asrt.iter_cons]
    constructor <;>
      · rintro ⟨h₁, h₂, rfl, hdisj, hPb, h₃, h₄, rfl, hdisj₂, hPa, hR⟩
        rw [PFun.disjoint_union_r] at hdisj
        refine ⟨h₃, h₁ ∪ h₄, ?_, ?_, hPa, h₁, h₄, rfl, hdisj.2, hPb, hR⟩
        · rw [← PFun.union_assoc, PFun.union_comm hdisj.1, PFun.union_assoc]
        · simp [hdisj.1.symm, hdisj₂]
  | trans _ _ ih₁ ih₂ => exact (ih₁ h).trans (ih₂ h)

theorem hIter_subperm {X : Type u} (P : X → Asrt) {xs ys : List X} {h : Heap}
    (hsub : ys.Subperm xs) (hIter : HProp h (Asrt.iter xs P)) :
    ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ HProp h₁ (Asrt.iter ys P) := by
  obtain ⟨l, hl_perm, hl_sub⟩ := hsub
  obtain ⟨zs, hperm⟩ := hl_sub.exists_perm_append
  rw [hIter_perm P h (hperm.trans (hl_perm.append_right zs)), hIter_app] at hIter
  obtain ⟨h₁, h₂, rfl, hdisj, hys, _⟩ := hIter
  exact ⟨h₁, h₂, rfl, hdisj, hys⟩

theorem hIter_elem_of {X : Type u} (P : X → Asrt) {x : X} {xs : List X} {h : Heap}
    (hin : x ∈ xs) (hIter : HProp h (Asrt.iter xs P)) :
    ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ HProp h₁ (P x) := by
  obtain ⟨h₁, h₂, rfl, hdisj, hx⟩ :=
    hIter_subperm P (List.singleton_subperm_iff.mpr hin) hIter
  exact ⟨h₁, h₂, rfl, hdisj, (hIter_singleton P x h₁).mp hx⟩

/-! ### Properties: weakening -/

theorem hPure_weaken (P : Asrt) (Q : Prop) (h : Heap) : HProp h (P ∗ ⌞Q⌟ →ₕ P) := by
  rintro ⟨h₁, h₂, rfl, hdisj, hP, rfl, _⟩
  simpa using hP

theorem hTrue_weaken (P : Asrt) (h : Heap) : HProp h (.true ∗ P →ₕ .true) :=
  fun _ => trivial

theorem hAffine_weaken (P Q : Asrt) (h : Heap) : HProp h (⌜P⌝ ∗ Q →ₕ ⌜P⌝) := by
  intro hStar
  rw [show HProp h ((P ∗ .true) ∗ Q) ↔ HProp h (P ∗ (.true ∗ Q)) from hStar_assoc]
    at hStar
  obtain ⟨h₁, h₂, rfl, hdisj, hP, _⟩ := hStar
  exact ⟨h₁, h₂, rfl, hdisj, hP, trivial⟩

/-! ### Properties: implication -/

theorem hImplies_refl (P : Asrt) : ⊨ (P →ₕ P) :=
  fun _ hP => hP

theorem hEmpty_left (P : Asrt) : ⊨ (P ∗ .emp →ₕ P) := by
  rintro h ⟨h₁, h₂, rfl, hdisj, hP, (rfl : h₂ = ∅)⟩
  simpa using hP

theorem hEmpty_right (P : Asrt) : ⊨ (P →ₕ P ∗ .emp) :=
  fun h hP => ⟨h, ∅, (PFun.union_empty h).symm, PFun.disjoint_empty_r h, hP, rfl⟩

end RUXt
