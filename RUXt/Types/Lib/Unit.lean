/-
Port of `theories/types/lib/unit.v`: the `unit` type.
-/
import RUXt.Types.Ty

namespace RUXt

open scoped RUXt.PMap

/-- The unit type (`unit`). -/
def unit : Ty where
  size := 1
  own vs :=
    match vs with
    | [.unit] => ⌞True⌟
    | _ => ⌞False⌟
  size_eq := by
    intro vs;
    rcases vs with ( _ | ⟨ v, _ | ⟨ w, vs ⟩ ⟩ ) <;> simp_all +decide;
    · exact fun h => by tauto;
    · intro h;
      cases v <;> simp +decide [ hprop ];
    · exact fun h _ => by tauto;

end RUXt