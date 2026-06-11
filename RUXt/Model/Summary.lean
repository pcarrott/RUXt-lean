/-
Port of `theories/model/summary.v`: summary contexts and properties.
-/
import RUXt.Lib.PMap
import RUXt.Lang.Assertion
import RUXt.Model.TypeChecker
import RUXt.Model.Logic

namespace RUXt

/-! ### Summaries for type spaces -/

/-- `concrete_summary` (`mk_summary`). -/
structure ConcreteSummary : Type 1 where
  post : Asrt
  src : Expr

/-- `summary`. -/
abbrev Summary := Val → ConcreteSummary

/-- `base_summary`. -/
def baseSummary (kind : BaseType) : Summary :=
  fun v => ⟨valPost kind v, .pure (.val v)⟩

/-! ### Summary contexts

In the Rocq development summary contexts are `gmap tid (list summary)`
accessed exclusively through the total lookup `!!!` (defaulting to `[]`);
total functions into lists are the faithful counterpart. -/

/-- Summary contexts (`summ_ctx`). -/
def SummCtx := Tid → List Summary

instance : EmptyCollection SummCtx := ⟨fun _ => []⟩

/-- `insert_base_summary`. -/
def insertBaseSummary (kind : BaseType) (S : SummCtx) : SummCtx :=
  Function.update S (.base kind) [baseSummary kind]

/-- `base_summ_ctx`: the initial summary context, registering the base summary
for each base type (built by folding `insertBaseSummary` over the base kinds in
the Rocq development). -/
def baseSummCtx : SummCtx :=
  [BaseType.int, .bool, .loc, .unit].foldr insertBaseSummary ∅

/-- `lookup_total_base`. -/
theorem baseSummCtx_base (kind : BaseType) :
    baseSummCtx (.base kind) = [baseSummary kind] := by
  cases kind <;> simp [baseSummCtx, insertBaseSummary, Function.update]

/-- `lookup_total_custom`. -/
theorem baseSummCtx_custom (n : String) : baseSummCtx (.custom n) = [] := by
  simp [baseSummCtx, insertBaseSummary, Function.update]
  rfl

/-- `update` (adds one summary for `τ`, as `partial_alter (summ_cons ς)` does). -/
def SummCtx.update (ς : Summary) (τ : Tid) (S : SummCtx) : SummCtx :=
  Function.update S τ (ς :: S τ)

/-- `subseteq` (`Σ [⊆] Σ'`). -/
def SummCtx.Subseteq (S S' : SummCtx) : Prop := ∀ τ, S τ ⊆ S' τ

@[inherit_doc] scoped infix:50 " [⊑] " => SummCtx.Subseteq

/-- `lookup_total_update`. -/
theorem SummCtx.update_apply (S : SummCtx) (τ : Tid) (ς : Summary) :
    S.update ς τ τ = ς :: S τ :=
  Function.update_self ..

/-- `lookup_total_update_ne`. -/
theorem SummCtx.update_apply_ne (S : SummCtx) {τ τ' : Tid} (ς : Summary) (h : τ ≠ τ') :
    S.update ς τ τ' = S τ' :=
  Function.update_of_ne (Ne.symm h) ..

/-! ### Flattening summary contexts

The Rocq development flattens a summary context into a list of pairs using
`map_fold`, whose defining property is `elem_of_flat`. With total-function
contexts, the faithful counterpart of that list is the *set of entries*
`flatSummCtx`, for which `elem_of_flat` holds definitionally. -/

/-- `flatten`. -/
def flatten (τ : Tid) (ςs : List Summary) : List (Tid × Summary) :=
  ςs.map (τ, ·)

/-- `flat_summ_ctx` (as the set of entries of the summary context). -/
def flatSummCtx (S : SummCtx) : Set (Tid × Summary) :=
  {τς | τς.2 ∈ S τς.1}

/-- `elem_of_flatten`. -/
theorem elem_of_flatten {τς : Tid × Summary} {τ : Tid} {ςs : List Summary} :
    τς ∈ flatten τ ςs ↔ τ = τς.1 ∧ τς.2 ∈ ςs := by
  obtain ⟨τ', ς'⟩ := τς
  simp only [flatten, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨ς'', hin, rfl, rfl⟩
    exact ⟨rfl, hin⟩
  · rintro ⟨rfl, hin⟩
    exact ⟨ς', hin, rfl, rfl⟩

/-- `elem_of_flat`. -/
theorem elem_of_flat {S : SummCtx} {τ : Tid} {ς : Summary} :
    (τ, ς) ∈ flatSummCtx S ↔ ς ∈ S τ :=
  Iff.rfl

end RUXt
