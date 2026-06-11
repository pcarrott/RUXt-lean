/-
Port of `theories/types/type.v`: generic type definition, assertions for type
ownership.
-/
import RUXt.Lang.Lang
import RUXt.Lang.Assertion

namespace RUXt

open scoped RUXt.PMap

/-! ### Type system -/

/-- Language types à la RustBelt (`type`). `τ.own vs` (Rocq `⟦ τ ⟧(vs)`) is the
ownership assertion of the type. -/
structure Ty : Type 1 where
  size : ℕ
  own : List Val → Asrt
  size_eq : ∀ vs, own vs ⊨ ⌞vs.length = size⌟

/-- Function types (`fun_type`, Rocq notation `{ τs ↣ τ }`). -/
structure FunType : Type 1 where
  tyIn : List Ty
  tyOut : Ty

/-- Type contexts. -/
abbrev TypeCtx := PMap String FunType

/-! ### Type assignment -/

/-- `typing` (`v ⊲ τ`). -/
inductive Typing : Type 1
  /-- The value `v` has type `τ` (Rocq `v ⊲ τ`). -/
  | own (v : Val) (τ : Ty)

@[inherit_doc] scoped infix:55 " ⊲ " => Typing.own

/-- `vs [⊲] τs`. -/
def typings (vs : List Val) (τs : List Ty) : List Typing :=
  List.zipWith Typing.own vs τs

@[inherit_doc] scoped infix:55 " [⊲] " => typings

/-- `TyOwn_eq_inj` (`Inj2`). -/
@[simp] theorem Typing.own_inj {v v' : Val} {τ τ' : Ty} :
    v ⊲ τ = v' ⊲ τ' ↔ v = v' ∧ τ = τ' := by
  grind +qlia

/-! ### Type interpretation -/

/-- `own_type`. -/
def ownType : Typing → Asrt
  | v ⊲ τ => τ.own [v]

/-- `[∗ₜ 𝕋]`: affine ownership of a list of typings. -/
def iterOwnTypes (𝕋 : List Typing) : Asrt := ⌜Asrt.iter 𝕋 ownType⌝

@[inherit_doc] scoped notation "[∗ₜ " 𝕋 "]" => iterOwnTypes 𝕋

/-- `own_typings`. -/
theorem own_typings {𝕋 : List Typing} {h𝕋 : Heap}
    (h : hprop h𝕋 (Asrt.iter 𝕋 ownType)) : hprop h𝕋 ([∗ₜ 𝕋]) := by
  contrapose! h;
  intro h';
  refine' h _;
  use h𝕋;
  use ∅; simp [h']

end RUXt