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
def SummCtx.Mem : SummCtx → Ty → Summary → Prop
  | S, τ, ς => ς ∈ S τ

theorem SummCtx.mem_update {S : SummCtx} {τ τ' : Ty} {ς ς' : Summary}
    (h : (S.update τ' ς').Mem τ ς) : τ = τ' ∧ ς = ς' ∨ S.Mem τ ς := by
  simp [SummCtx.Mem, SummCtx.update] at h
  by_cases hτ : τ = τ'
  · rw [<- hτ] at h
    rw [Function.update_self] at h
    rw [List.mem_cons] at h
    rcases h with ⟨hς⟩ | h
    · exact Or.inl ⟨hτ, hς⟩
    · exact Or.inr h
  · rw [Function.update_of_ne hτ] at h
    exact Or.inr h

/-- The state `[ε:Φ]` is reachable from safe main `[e:τ]`. -/
def ReachableFromMain {tt : Tele} (Λ : Library) (τ : Ty)
    (e : tt -t> Expr) (ε : LExit) (Φ : Val → tt -t> Asrt) : Prop :=
  (∀ args, SafeMain Λ (e.apply args) τ) ∧
  UXFrameTriple Λ ⟨teleBind fun _ ↦ Asrt.emp, e, ε, Φ⟩
/-- Semantic interpretation of valid summaries. -/
def ValidSummary (Λ : Library) (τ : Ty) (ς : Summary) : Prop :=
  ReachableFromMain Λ τ ς.src .lok ς.post ∧ ∃ v args, Sat ((ς.post v).apply args)
/-- Semantic interpretation of valid summary contexts. -/
def ValidSummCtx (Λ : Library) (S : SummCtx) : Prop :=
  ∀ τ ς, S.Mem τ ς → ValidSummary Λ τ ς

/-- Summary selection. -/
abbrev SummPicks := List (Ty × Summary)
/-- `Σ [⊐] ςs`: `ςs` is a list of summaries valid in context `Σ`. -/
def SummCtx.validPicks (S : SummCtx) (ςs : SummPicks) : Prop :=
  ∀ τ ς, (τ, ς) ∈ ςs → ς ∈ S τ
@[inherit_doc] scoped infix:50 " [⊐] " => SummCtx.validPicks

/-- Each picked summary is valid in a valid context. -/
theorem summPicks_valid {Λ : Library} {S : SummCtx} {ςs : SummPicks}
    (hsumm : ValidSummCtx Λ S) (hsub : S [⊐] ςs) :
    ∀ τ ς, (τ, ς) ∈ ςs → ValidSummary Λ τ ς :=
  fun τ ς h => hsumm τ ς (hsub τ ς h)

theorem validPicks_cons {S : SummCtx} {τ : Ty} {ς : Summary} {ςs : SummPicks} :
  S [⊐] (τ, ς) :: ςs ↔ S [⊐] ςs ∧ ς ∈ S τ := by
  constructor
  · tauto
  · intro ⟨hsub, hmem⟩ τ ς hin; simp at hin
    rcases hin with ⟨rfl, rfl⟩ | hin
    · exact hmem
    · exact hsub τ ς hin

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

theorem baseSummCtx_base {kind : BaseType} {ς : Summary}
    (hval : baseSummCtx.Mem (.base kind) ς) : ς = baseSummary kind := by
  simp [SummCtx.Mem, baseSummCtx, SummCtx.update] at hval
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

theorem baseSummCtx_custom {n : String} {ς : Summary}
    (hval : baseSummCtx.Mem (.custom n) ς) : False := by
  contradiction

theorem baseSummary_valid Λ kind :
    ValidSummary Λ (Ty.base kind) (baseSummary kind) := by
  constructor
  · constructor
    · cases kind <;> exact fun _ => safeMain_pure
    · cases kind <;> simp [baseSummary]
      · intro args v h' hΦ
        simp_all [TeleFun.apply]
        exact ⟨∅, by tauto, by tauto⟩
      · intro args v h' hΦ
        simp_all [TeleFun.apply]
        exact ⟨∅, by tauto, by tauto⟩
      · intro args v h' hΦ
        simp_all [TeleFun.apply]
        exact ⟨∅, by tauto, by tauto⟩
      · intro args v h' hΦ
        simp_all [TeleFun.apply]
        exact ⟨∅, by tauto, by tauto⟩
  · cases kind
    · exact ⟨Val.int 0, ⟨0, PUnit.unit⟩, ∅, by tauto⟩
    · exact ⟨.bool true, ⟨true, PUnit.unit⟩, ∅, by tauto⟩
    · exact ⟨.loc (0, 0), ⟨(0, 0), PUnit.unit⟩, ∅, by tauto⟩
    · exact ⟨.unit, PUnit.unit, ∅, by tauto⟩

/-! ### Summary composition -/

/-- `tt.Merge ς A`: the type of a telescopic function over `ς`'s telescope
prefixed by a fresh value binder, then appended with `tt`, returning `A`. -/
def Tele.Merge : Tele → Summary → Type v → Type v
  | tt, ς, A => TeleFun.{0, v}
    ((Tele.cons fun _ : Val => ς.tele_of).app tt) A
/-- `f.mergePost ς`: prepend `f` with `ς`, composing result of `ς.post` and
the result of `f` using the separating conjunction `∗`. -/
def TeleFun.mergePost {tt : Tele} :
    (tt -t> Asrt) → (ς : Summary) → tt.Merge ς Asrt
  | f, ς => fun v => teleMerge (fun x y => x ∗ y) (ς.post v) f
/-- `f.mergeVals ς`: prepend `f` with `ς`, consing the value `v` of `ς.post`
to the result `vs` of `f`. -/
def TeleFun.mergeVals {tt : Tele} :
    (tt -t> (List Val)) → (ς : Summary) → tt.Merge ς (List Val)
  | f, ς => fun v => teleMerge (fun _ vs => v :: vs) (ς.post v) f
/-- `f.mergeSrc ς b`: prepend `f` with `ς`, binding `b` to the result `e` of `ς.src`
in the result `body` of `f`. -/
def TeleFun.mergeSrc {tt : Tele} :
    (tt -t> Expr) → (ς : Summary) → Binder → tt.Merge ς Expr
  | body, ς, b => fun _ => teleMerge (fun e body => .letIn b e body) ς.src body

/-- `Tele.triple ςs`: the combined telescope obtained by appending, for each summary in ςs,
a fresh value binder followed by that summary's telescope. -/
def Tele.triple (ςs : SummPicks) : Tele :=
  (ςs.map (fun ς => Tele.cons fun _ : Val => ς.2.tele_of)).foldr Tele.app Tele.nil
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

@[simp] theorem mergePosts_nil (arg : TeleArg (Tele.triple [])) :
    (mergePosts []).apply arg = Asrt.emp := rfl
@[simp] theorem mergeVals_nil (arg : TeleArg (Tele.triple [])) :
    (mergeVals []).apply arg = [] := rfl
@[simp] theorem mergeSrcs_nil (xs : List String) (e : Expr) (arg : TeleArg (Tele.triple [])) :
    (mergeSrcs xs [] e).apply arg = e := rfl

theorem mergePosts_cons (τ : Ty) (ς : Summary) (ςs : SummPicks) (v : Val)
    (rest : TeleArg (ς.tele_of.app (Tele.triple ςs))) :
    (mergePosts ((τ, ς) :: ςs)).apply ⟨v, rest⟩
      = (ς.post v).apply rest.fst ∗ (mergePosts ςs).apply rest.snd := by
  simp [mergePosts, TeleFun.mergePost, TeleFun.apply, teleMerge_apply_eq]
theorem mergeVals_cons (τ : Ty) (ς : Summary) (ςs : SummPicks) (v : Val)
    (rest : TeleArg (ς.tele_of.app (Tele.triple ςs))) :
    (mergeVals ((τ, ς) :: ςs)).apply ⟨v, rest⟩ = v :: (mergeVals ςs).apply rest.snd := by
  simp [mergeVals, TeleFun.mergeVals, TeleFun.apply, teleMerge_apply_eq]
theorem mergeSrcs_cons (xs : List String) (τ : Ty) (ς : Summary) (ςs : SummPicks)
    (e : Expr) (v : Val) (rest : TeleArg (ς.tele_of.app (Tele.triple ςs))) :
    (mergeSrcs xs ((τ, ς) :: ςs) e).apply ⟨v, rest⟩
      = .letIn (match xs.head? with | some x => .named x | none => .anon)
          (ς.src.apply rest.fst) ((mergeSrcs xs.tail ςs e).apply rest.snd) := by
  simp [mergeSrcs, TeleFun.mergeSrc, TeleFun.apply, teleMerge_apply_eq]

theorem mergeVals_length : ∀ (ςs : SummPicks) (args : TeleArg (Tele.triple ςs)),
    ((mergeVals ςs).apply args).length = ςs.length := by
  intro ςs
  induction' ςs with ς ςs ih
  · simp
  · intro ⟨v, rest⟩
    rw [mergeVals_cons]; simp
    exact ih _

end RUXt
