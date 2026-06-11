/-
Port of `theories/types/lib/own.v`: owned-pointer types.
-/
import RUXt.Lang.Semantics
import RUXt.Types.Ty

namespace RUXt

open scoped RUXt.PMap

/-- Owned pointers (`own`): a pointer to a cell that contains a value of type
`τ` (if `τ = some _`), or to a possibly uninitialised cell (if `τ = none`). -/
def own (τ : Option Ty) : Ty where
  size := 1
  own vs :=
    match vs with
    | [.loc l] =>
        match τ with
        | some τ => .ex fun v => (l ↦ v) ∗ τ.own [v]
        | none => (l ↦?) ∨ₕ .ex fun v => l ↦ v
    | _ => ⌞False⌟
  size_eq := by
    rintro ( _ | ⟨ _, _ | ⟨ _, _ ⟩ ⟩ ) <;> simp
    · exact fun h _ => by tauto
    · intro h hp
      exact ⟨ ∅, by simp +decide, by simp +decide [ hprop ] ⟩
    · tauto

/-- `empty`: a pointer to a possibly uninitialised cell. -/
def empty : Ty := own none

/-- `box τ`: a pointer to a cell holding a `τ`. -/
def box (τ : Ty) : Ty := own (some τ)

/-- `boxes τs`. -/
def boxes (τs : List Ty) : List Ty := τs.map box

/-! ### Properties -/

/-- `own_uninit`. -/
theorem own_uninit {h : Heap} {l : Loc} (hown : hprop h (empty.own [.loc l])) :
    l.2 = 0 ∧ ∃ hv, h = PMap.singleton l.1 (.block 1 (PMap.singleton l.2 hv)) := by
  obtain ⟨ h₀, h₁ ⟩ := hown
  · exact ⟨ h₁, _, h₀ ⟩
  · obtain ⟨ v, hv ⟩ := ‹_›
    obtain ⟨ h₀, h₁ ⟩ := hv
    exact ⟨ h₁, _, h₀ ⟩

/-- `own_box`. -/
theorem own_box {h : Heap} {l : Loc} {τ : Ty} (hown : hprop h ((box τ).own [.loc l])) :
    l.2 = 0 ∧ ∃ hv, h l.1 = some (.block 1 (PMap.singleton l.2 hv)) := by
  rcases hown with ⟨ h₀, h₁, ⟨ v, hv ⟩ ⟩
  have := hv.2.2.1; simp_all +decide

/-- `own_loc`. -/
theorem own_loc {h : Heap} {l : Loc} {τ : Option Ty} (hown : hprop h ((own τ).own [.loc l])) :
    l.2 = 0 ∧ ∃ hv, h l.1 = some (.block 1 (PMap.singleton l.2 hv)) := by
  unfold own at hown
  cases τ <;> simp_all +decide [ hprop ]
  · cases hown <;> aesop
  · obtain ⟨ x, h₂, rfl, h₂', hl₂, hx ⟩ := hown
    exact ⟨ hl₂, HeapValue.val x, by simp +decide ⟩

end RUXt
