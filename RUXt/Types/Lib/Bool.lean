/-
Port of `theories/types/lib/bool.v`: the `bool` type.
-/
import RUXt.Types.Ty

namespace RUXt

open scoped RUXt.PMap

/-- The type of booleans (`bool`). -/
def bool : Ty where
  size := 1
  own vs :=
    match vs with
    | [.bool _] => ⌞True⌟
    | _ => ⌞False⌟
  size_eq := by
    intro vs h
    rcases vs with ( _ | ⟨ v, _ | ⟨ w, vs ⟩ ⟩ ) <;> simp_all +decide

end RUXt