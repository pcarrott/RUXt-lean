import Mathlib.Tactic

/-!
# Telescopes
A telescope `Tele` describes a (dependent) sequence of arguments. Given a telescope `TT`,
`TeleFun TT A` (notation `TT -t> A`) is the type of curried functions taking exactly the
arguments described by `TT` and returning an `A`, while `TeleArg TT` is the type of a
single "argument tuple" for `TT`. `TeleFun.apply` applies a telescopic function to such a
tuple.

## Universe polymorphism
The definitions here are *universe polymorphic*.  A telescope `Tele.{u}` stores
binder types in `Type u`, while the result type `A` of a telescopic function lives in
`Type (max u v)` for an independent universe parameter `v`.  Concretely, this lifts
the restriction that the result of `TT -t> A` must live in `Type` (i.e. `Type 0`).
Lean 4 has no universe cumulativity, so the result universe must be at least the universe
of the telescope's binders; phrasing the result type as `Type (max u v)` captures exactly
this requirement while leaving both `u` and `v` free.
-/

namespace RUXt

universe u v w x

/-- A telescope: an inductively defined, possibly dependent, sequence of argument types.
The binder types live in an arbitrary universe `Type u`. -/
inductive Tele : Type (u + 1) where
  /-- The empty telescope (`TeleO`). -/
  | nil : Tele
  /-- Extend a telescope by a fresh argument of type `X`, whose value may influence the
  remaining telescope `binder x` (`TeleS`). -/
  | cons {X : Type u} (binder : X → Tele) : Tele

/-- The telescope version of a function type: `TeleFun TT A` is the type of functions
taking the arguments described by `TT` and returning `A` (notation `TT -t> A`).
The result type `A` may live in any universe `Type (max u v)`, i.e. any universe at least
as large as the universe `u` of the telescope's binders. In particular `A` is **not**
restricted to `Type 0`. -/
def TeleFun : Tele.{u} → Type (max u v) → Type (max u v)
  | Tele.nil, A => A
  | Tele.cons binder, A => ∀ x, TeleFun (binder x) A
@[inherit_doc] infixr:25 " -t> " => TeleFun

/-- A sigma-like type for an "element" of a telescope `TT`, i.e. the data needed to obtain
an `A` from a `TT -t> A`. -/
def TeleArg : Tele.{u} → Type u
  | Tele.nil => PUnit
  | Tele.cons binder => Σ x, TeleArg (binder x)

/-- Apply a telescopic function to an argument tuple. -/
def TeleFun.apply : {TT : Tele.{u}} → {A : Type (max u v)} → (TT -t> A) → TeleArg TT → A
  | Tele.nil, _, t, _ => t
  | Tele.cons _, _, f, a => apply (f a.1) a.2

/-- Map a function over the result of a telescopic function. -/
def TeleFun.map {A : Type (max u v)} {B : Type (max u w)} :
    {TT : Tele.{u}} → (TT -t> A) → (A → B) → (TT -t> B)
  | Tele.nil, t, F => F t
  | Tele.cons _, t, F => fun x => map (t x) F

/-- Turn an ordinary function on argument tuples into a telescopic function. -/
def teleBind : {TT : Tele.{u}} → {A : Type (max u v)} → (TeleArg TT → A) → (TT -t> A)
  | Tele.nil, _, F => F PUnit.unit
  | Tele.cons _, _, F => fun x => teleBind (fun a => F ⟨x, a⟩)

/-- Telescopic application and mapping commute. -/
theorem teleMap_apply {A : Type (max u v)} {B : Type (max u w)} (F : A → B) :
    {TT : Tele.{u}} → (t : TT -t> A) → (y : TeleArg TT) →
      (t.map F).apply y = F (t.apply y)
  | Tele.nil, _, _ => rfl
  | Tele.cons _, t, y => teleMap_apply F (t y.1) y.2

/-- Application to a bound telescopic function recovers the original function. -/
theorem teleBind_apply {A : Type (max u v)} :
    {TT : Tele.{u}} → (f : TeleArg TT → A) → (x : TeleArg TT) →
      (teleBind f).apply x = f x
  | Tele.nil, f, x => by
      cases x; rfl
  | Tele.cons _, f, x => by
      cases x with
      | mk x a => exact teleBind_apply (fun a => f ⟨x, a⟩) a

/-- Concatenate two telescopes. -/
def Tele.app : Tele.{u} → Tele.{u} → Tele.{u}
  | Tele.nil, tt2 => tt2
  | Tele.cons b, tt2 => Tele.cons (fun x => app (b x) tt2)

/-- Merge two telescopic functions over appended telescopes using a binary combiner. -/
def teleMerge {A : Type (max u v)} {B : Type (max u w)} {C : Type (max u x)}
    (merge : A → B → C) :
    {tt1 tt2 : Tele.{u}} → (tt1 -t> A) → (tt2 -t> B) → (tt1.app tt2 -t> C)
  | Tele.nil, _, P1, P2 => P2.map (fun P => merge P1 P)
  | Tele.cons _, _, P1, P2 => fun y => teleMerge merge (P1 y) P2

/-- Specification of application to a merged telescopic function. -/
theorem teleMerge_apply {tt1 tt2 : Tele.{u}} {A : Type (max u v)} {B : Type (max u w)}
    {C : Type (max u x)} (merge : A → B → C)
    (f : tt1 -t> A) (g : tt2 -t> B) (P : B → Prop) (Q : C → Prop)
    (HP2 : ∀ args', P (g.apply args')) (Hmerge : ∀ a b, P b → Q (merge a b)) :
    ∀ args, Q ((teleMerge merge f g).apply args) := by
  revert f g
  induction' tt1 with b ih
  · intro f g hg args
    convert Hmerge f (g.apply args) (hg args) using 1
    convert teleMap_apply (fun y => merge f y) g args using 1
  · grind +locals

/-!
## The `[tele ...]` notation
We provide a term notation `[tele (x : A) (y : B) ...]` for *building* a telescope value,
i.e. an element of `Tele`. It expands to the corresponding chain of `Tele.cons`/`Tele.nil`:
```
[tele (x : A) (y : B)]  ↝  Tele.cons (fun x : A => Tele.cons (fun y : B => Tele.nil))
[tele]                  ↝  Tele.nil
```
The binders may be dependent (e.g. `[tele (n : Nat) (_ : Fin n)]`) and `_` is allowed for
anonymous binders.

Note on tokenisation: we keep `[` and `tele` as two separate tokens rather than a
single `[tele` atom.  A single `[tele` atom would be lexed greedily and would break
ordinary list literals whose first element is an identifier starting with `tele` (e.g.
`[telescope, x]`).  Keeping them separate makes `tele` a keyword that only triggers
the notation right after an opening `[`, while still allowing such list literals. -/
open Lean Parser Term in
syntax (name := teleNotation) "[" "tele" (ppSpace funBinder)* "]" : term
macro_rules
  | `([tele $bs:funBinder*]) => do
      let mut e ← `(RUXt.Tele.nil)
      for b in bs.reverse do
        e ← `(RUXt.Tele.cons (fun $b => $e))
      return e

end RUXt
