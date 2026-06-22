namespace RUXt

/-- Base types for values. -/
inductive BaseType
  | int
  | bool
  | loc
  | unit
deriving DecidableEq

/-- Identifiers for named types. -/
abbrev Tid := String
/-- Types: base types or named custom types. -/
inductive Ty
  | base (kind : BaseType)
  | custom (name : Tid)
deriving DecidableEq

end RUXt
