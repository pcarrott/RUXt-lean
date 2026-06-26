import RUXt.Lib.PFun
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
def Library := PFun Fid FunImpl

/-- Function `f` exists in library `Λ` with implementation `γ` -/
def Library.MapsTo (Λ : Library) (f : Fid) (γ : FunImpl) : Prop :=
  Λ f = γ

end RUXt
