import RUXt.Lib.PMap
import RUXt.Lang.Types
import RUXt.Lang.Lang

namespace RUXt

/-- Function implementations. -/
structure FunImpl where
  params : List (PVar × Ty)
  body : Expr
  ty : Ty
  paramsNodup : (params.map Prod.fst).Nodup

/-- Libraries map function identifiers to their implementations. -/
def Library := PMap Fid FunImpl

/-- Get the implementation of a function by its identifier. -/
def Library.get : Library → Fid → Option FunImpl
  | Λ, f => Λ f

end RUXt
