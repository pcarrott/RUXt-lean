import RUXt.Lib.Telescopes
import RUXt.Lang.TypeChecker
import RUXt.Model.Logic

namespace RUXt

universe v

/-! ### Type subvariants -/

/-- A summary for a type space. -/
structure Summary where
  /-- The telescope of arguments the summary is parameterised over. -/
  tele_of : Tele.{0}
  /-- The telescopic postcondition, depending on a value. -/
  post : Val → TeleFun.{0, v + 1} tele_of Asrt.{v}
  /-- The telescopic source expression. -/
  src : TeleFun.{0, 0} tele_of Expr

/-- Context under-approximating the type spaces. -/
def SummCtx := Ty → List Summary
instance : EmptyCollection SummCtx := ⟨fun _ => []⟩
def SummCtx.update : SummCtx → Ty → Summary → SummCtx
  | S, τ, ς => Function.update S τ (ς :: S τ)
def SummCtx.mem : SummCtx → Ty → Summary → Prop
  | S, τ, ς => ς ∈ S τ

theorem SummCtx.memUpdate {S : SummCtx} {τ τ' : Ty} {ς ς' : Summary}
    (h : (S.update τ' ς').mem τ ς) : τ = τ' ∧ ς = ς' ∨ S.mem τ ς := by
  simp [SummCtx.mem, SummCtx.update] at h
  by_cases hτ : τ = τ'
  · rw [<- hτ] at h
    rw [Function.update_self] at h
    rw [List.mem_cons] at h
    rcases h with ⟨hς⟩ | h
    · exact Or.inl ⟨hτ, hς⟩
    · exact Or.inr h
  · rw [Function.update_of_ne hτ] at h
    exact Or.inr h

/-- The state [`ε` : `Φ`] is reachable from safe main [`e` : `τ`]. -/
def ReachableFromMain {tt : Tele} (Λ : Library) (τ : Ty)
    (e : tt -t> Expr) (ε : LExit) (Φ : Val → tt -t> Asrt) : Prop :=
  (∀ args, safeMain Λ (e.apply args) = some τ) ∧
  UXFrameTriple Λ ⟨teleBind fun _ ↦ Asrt.emp, e, ε, Φ⟩
/-- Semantic interpretation of valid summaries. -/
def ValidSummary (Λ : Library) (τ : Ty) (ς : Summary) : Prop :=
  ReachableFromMain Λ τ ς.src .lok ς.post ∧ ∃ v args, sat ((ς.post v).apply args)
/-- Semantic interpretation of valid summary contexts. -/
def ValidSummCtx (Λ : Library) (S : SummCtx) : Prop :=
  ∀ τ ς, S.mem τ ς → ValidSummary Λ τ ς

/-! ### Type spaces for base types -/

/-- Constructs a summary given a base type. -/
def baseSummary : BaseType → Summary
  | .int => ⟨[tele (_ : ℤ)], fun r z => ⌞ r = .int z ⌟, fun z => Expr.int z⟩
  | .bool => ⟨[tele (_ : Bool)], fun r b => ⌞ r = .bool b ⌟, fun b => Expr.bool b⟩
  | .loc => ⟨[tele (_ : Loc)], fun r l => ⌞ r = .loc l ⌟, fun l => Expr.loc l⟩
  | .unit => ⟨[tele], fun r => ⌞ r = .unit ⌟, Expr.unit⟩

/-- The exact type spaces for all base types. -/
def baseSummCtx : SummCtx :=
  [.int, .bool, .loc, .unit].foldr (fun kind S => S.update (.base kind) (baseSummary kind)) ∅

theorem baseSummCtxBase {kind : BaseType} {ς : Summary}
    (hval : baseSummCtx.mem (.base kind) ς) : ς = baseSummary kind := by
  simp [SummCtx.mem, baseSummCtx, SummCtx.update] at hval
  cases kind
  · rw [Function.update_self] at hval
    cases hval; rfl; contradiction
  · rw [Function.update_of_ne] at hval
    · rw [Function.update_self] at hval
      cases hval; rfl; contradiction
    · intro h; cases h
  · rw [Function.update_of_ne] at hval
    · rw [Function.update_of_ne] at hval
      · rw [Function.update_self] at hval
        cases hval; rfl; contradiction
      · intro h; cases h
    · intro h; cases h
  · rw [Function.update_of_ne] at hval
    · rw [Function.update_of_ne] at hval
      · rw [Function.update_of_ne] at hval
        · rw [Function.update_self] at hval
          cases hval; rfl; contradiction
        · intro h; cases h
      · intro h; cases h
    · intro h; cases h

theorem baseSummCtxCustom {n : String} {ς : Summary}
    (hval : baseSummCtx.mem (.custom n) ς) : False := by
  contradiction

theorem baseSummaryValid Λ kind :
    ValidSummary Λ (Ty.base kind) (baseSummary kind) := by
  sorry

/-! ### Summary selection and composition -/

abbrev SummPicks := List (Ty × Summary)

/-- `ςs [⊆] Σ`: `ςs` is a list of summaries valid in context `Σ`. -/
def SummCtx.validPicks (S : SummCtx) (ςs : SummPicks) : Prop :=
  ∀ τ ς, (τ, ς) ∈ ςs → ς ∈ S τ
@[inherit_doc] scoped infix:50 " [⊐] " => SummCtx.validPicks

/-- `tt.merge ς A`: the type of a telescopic function over `ς`'s telescope
prefixed by a fresh value binder, then appended with `tt`, returning `A`. -/
def Tele.merge : Tele → Summary → Type v → Type v
  | tt, ς, A => TeleFun.{0, v}
    ((Tele.cons fun _ : Val => ς.tele_of).app tt) A
/-- `f.mergeIgnore ς`: prepend `f` with `ς`, ignoring ς and keeping `f`'s result. -/
def TeleFun.mergeIgnore {tt : Tele} {A : Type v} :
    (tt -t> A) → (ς : Summary) → tt.merge ς A
  | f, ς => teleMerge (fun _ y => y) ς.post f
/-- `f.mergePost ς`: prepend `f` with `ς`, composing result of `ς.post` and
the result of `f` using separating conjunction `∗`. -/
def TeleFun.mergePost {tt : Tele} :
    (tt -t> Asrt) → (ς : Summary) → tt.merge ς Asrt
  | f, ς => fun v => teleMerge (fun x y => x ∗ y) (ς.post v) f
/-- `f.mergeVals ς`: prepend `f` with `ς`, consing the value `v` of `ς.post`
to the result `vs` of `f`. -/
def TeleFun.mergeVals {tt : Tele} :
    (tt -t> (List Val)) → (ς : Summary) → tt.merge ς (List Val)
  | f, ς => fun v => teleMerge (fun _ vs => v :: vs) (ς.post v) f
/-- `f.mergeSrc ς b`: prepend `f` with `ς`, binding `b` to the result `e` of `ς.src`
in the result `body` of `f`. -/
def TeleFun.mergeSrc {tt : Tele} :
    (tt -t> Expr) → (ς : Summary) → Binder → tt.merge ς Expr
  | body, ς, b => fun _ => teleMerge (fun e body => .letIn b e body) ς.src body

/-- `Tele.triple ςs`: the combined telescope obtained by appending, for each summary in ςs,
a fresh value binder followed by that summary's telescope. -/
def Tele.triple (ςs : SummPicks) : Tele :=
  (ςs.map (fun ς => Tele.cons fun _ : Val => ς.2.tele_of)).foldr Tele.app Tele.nil
/-- `mergeIgnore a  ςs`: the constant telescopic function returning `a`, with all summary
telescopes (and value binders) ignored. -/
def mergeIgnore {A : Type v} (a : A) :
    (ςs : SummPicks) → Tele.triple ςs -t> A
  | [] => a | (_, ς) :: ςs => (mergeIgnore a ςs).mergeIgnore ς
/-- `mergePosts ςs`: the separating conjunction of all summaries' postconditions, as a
telescopic assertion over `triple_tt ςs`. -/
def mergePosts : (ςs : SummPicks) → Tele.triple ςs -t> Asrt
  | [] => .emp | (_, ς) :: ςs => (mergePosts ςs).mergePost ς
/-- `mergeVals ςs`: the telescopic function collecting one value per summary into a list. -/
def mergeVals : (ςs : SummPicks) → Tele.triple ςs -t> List Val
  | [] => [] | (_, ς) :: ςs => (mergeVals ςs).mergeVals ς
/-- `mergeSrcs xs ςs e`: the telescopic source expression nesting the summaries' sources in
`Let`-bindings (named by `xs`), bottoming out at `e`. -/
def mergeSrcs : List String → (ςs : SummPicks) → Expr → Tele.triple ςs -t> Expr
  | _, [], e => e | xs, (_, ς) :: ςs, e => (mergeSrcs xs.tail ςs e).mergeSrc ς
    (match xs.head? with | some x => .named x | none => .anon)
/-- `mergePostsIgnore ςs ςs'`: like `mergePosts` for `ςs`, but the postconditions of `ςs'`
are ignored (their binders are kept). -/
def mergePostsIgnore : (ςs ςs' : SummPicks) → Tele.triple (ςs ++ ςs') -t> Asrt
  | [], ςs' => mergeIgnore Asrt.emp ςs'
  | (_, ς) :: ςs, ςs' => (mergePostsIgnore ςs ςs').mergePost ς
/-- `mergeValsIgnore ςs ςs'`: like `mergeVals` for `ςs`, but the values of `ςs'` are
ignored (their binders are kept). -/
def mergeValsIgnore : (ςs ςs' : SummPicks) → Tele.triple (ςs ++ ςs') -t> List Val
  | [], ςs' => mergeIgnore [] ςs'
  | (_, ς) :: ςs, ςs' => (mergeValsIgnore ςs ςs').mergeVals ς
/-- `mergeSrcsIgnore xs ςs ςs' e`: like `mergeSrcs` for `ςs'`, but the sources of `ςs` are
ignored (their binders are kept). -/
def mergeSrcsIgnore : List String → (ςs ςs' : SummPicks) → Expr → Tele.triple (ςs ++ ςs') -t> Expr
  | xs, [], ςs', e => mergeSrcs xs ςs' e
  | xs, (_, ς) :: ςs, ςs', e => (mergeSrcsIgnore xs ςs ςs' e).mergeIgnore ς

end RUXt
