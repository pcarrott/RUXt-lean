/-
Port of `theories/types/lib/int.v`: the `int` type.
-/
import RUXt.Types.Ty

namespace RUXt

open scoped RUXt.PMap

/-- The type of integers (`int`). -/
def int : Ty where
  size := 1
  own vs :=
    match vs with
    | [.int _] => ⌞True⌟
    | _ => ⌞False⌟
  size_eq := by
    intro vs;
    rintro h;
    rcases vs with ( _ | ⟨ v, _ | ⟨ w, _ | vs ⟩ ⟩ ) <;> simp_all +decide

end RUXt