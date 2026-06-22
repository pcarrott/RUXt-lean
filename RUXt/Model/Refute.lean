import RUXt.Model.Summary

namespace RUXt

/-! ### The type refutation algorithm -/

/-- Well-typed states that can be derived by some UX logic. -/
def DerivablePost (Λ : Library) (ςs : SummPicks) (f : Fid) (xs : List PVar)
    (τ : Ty) (ε : LExit) (Φ : Val → Tele.triple ςs -t> Asrt) : Prop :=
      -- Some function `f` outputs values of type `τ`
      ∃ params body hdup, Λ.get f = some ⟨params, body, τ, hdup⟩ ∧
      -- The concrete input types must match the types in `ςs`
      xs = params.map Prod.fst ∧ ςs.map Prod.fst = params.map Prod.snd ∧
      -- `[ε : Φ]` is obtained from executing `f` after composing the summaries in `ςs`
      ∃ L : Logic, L.DerivableSpec Λ
        ⟨mergePosts ςs, (mergeVals ςs).map (fun vs => .call f (Term.ofVals vs)), ε, Φ⟩

/-- Bind each summary in `ςs` to a variable in `xs` and calls `f` on `xs`. -/
def Witness (f : Fid) (xs : List PVar) (ςs : SummPicks) : Tele.triple ςs -t> Expr :=
  mergeSrcs xs ςs (.call f (Term.ofVars xs))

/-- The refutation procedure. -/
def TryRefute (Λ : Library) (S : SummCtx) (r : SummCtx ⊕ Expr) : Prop :=
  -- Pick a subset ςs of Σ, for input summaries
  ∃ ςs, S [⊐] ςs ∧
  -- Construct [e : τ] that terminates with postcondition [ε : Φ]
  ∃ f xs τ ε Φ, DerivablePost Λ ςs f xs τ ε Φ ∧
  -- The postcondition is satisfiable
  ∃ v args, sat ((Φ v).apply args) ∧
  -- Case analysis on whether the derived state is Ok
  match r with
  | .inl S' => ε = .lok ∧ -- Case Ok: The summary context Σ is updated to Σ'
        S' = SummCtx.update S τ ⟨Tele.triple ςs, Φ, Witness f xs ςs⟩
  -- Found witness `e` for type unsoundness
  | .inr e => ε ≠ .lok ∧ --Cases Err/Miss: Found witness e for type unsoundness
      e = (Witness f xs ςs).apply args

/-- Meta-loop for deriving well-formed contexts. -/
inductive WfSummCtx (Λ : Library) : SummCtx → Prop
  | nil :
      WfSummCtx Λ baseSummCtx
  | cons {S S' : SummCtx} :
      WfSummCtx Λ S → TryRefute Λ S (.inl S') →
      WfSummCtx Λ S'

/-! ### Inference soundness -/

/-- Any derivable state can be witnessed by a main program. -/
theorem DerivableForMain {Λ : Library} {S : SummCtx} {ςs : SummPicks} {f : Fid}
    {xs : List PVar} {τ : Ty} {ε : LExit} {Q : Val → Tele.triple ςs -t> Asrt}
    (hsumm : ValidSummCtx Λ S) (hsub : S [⊐] ςs)
    (hpost : DerivablePost Λ ςs f xs τ ε Q) :
    ReachableFromMain Λ τ (Witness f xs ςs) ε Q := by
  sorry

/-- Soundness of well-formed type summary contexts. -/
theorem SummCtxSoundness {Λ : Library} {S : SummCtx}
    (hsumm : WfSummCtx Λ S) : ValidSummCtx Λ S := by
  induction hsumm with
  | nil =>
    intro τ ς hin
    rcases τ with ⟨kind⟩
    · rw [baseSummCtxBase hin]
      exact baseSummaryValid Λ kind
    · contradiction
  | cons _ hrefute ih =>
    intro τ' ς' hin
    obtain ⟨ςs, hsub, f, xs, τ, ε, Φ, hpost, v, args, hsat, ⟨rfl, rfl⟩⟩ := hrefute
    rcases SummCtx.memUpdate hin with ⟨rfl, rfl⟩ | hin
    · exact ⟨DerivableForMain ih hsub hpost, v, args, hsat⟩
    · exact ih τ' ς' hin

/-! ### Soundness result of RUXt -/

/-- A type assignment in the library can be refuted. -/
def HasRefutedType (Λ : Library) (e : Expr) : Prop :=
  ∃ S, WfSummCtx Λ S ∧ TryRefute Λ S (.inr e)
/-- A main program exhibits undefined behaviour. -/
def Inadequate (Λ : Library) (e : Expr) : Prop :=
  ∃ h, (Λ ⊢ ⟨∅ | e⟩ ⇓ ⟨h | .err⟩) ∧ ∃ τ, safeMain Λ e = some τ

/-- Adequacy result for refuted type assignments. -/
theorem inadequacy {Λ : Library} {e : Expr}
    (hrefuted : HasRefutedType Λ e) : Inadequate Λ e := by
  obtain ⟨S, hctx, hrefute⟩ := hrefuted
  have hctx := SummCtxSoundness hctx
  obtain ⟨ςs, hsub, f, xs, τ, εₗ, Φ, hpost, r, args, ⟨h', hΦ⟩, ⟨Hnok, rfl⟩⟩ := hrefute
  obtain ⟨hsafe, hux⟩ := DerivableForMain hctx hsub hpost
  obtain ⟨_, _, _, _, _, _, L, hspec⟩ := hpost
  obtain hspec := L.ux_frame_soundness hspec
  obtain ⟨_, _, ε, ⟨hε, _⟩⟩ := hspec _ _ _ hΦ
  obtain ⟨h, hP, hstep⟩ := ux_frame_triple_spec hux _ _ _ hΦ _ hε
  rw [teleBind_apply] at hP
  rw [hP] at *
  refine ⟨h', ?_, τ, hsafe args⟩
  rcases εₗ
  · contradiction
  · let .unit := r
    injection hε with hε; subst hε
    exact hstep
  · let .loc _ := r
    injection hε with hε; subst hε
    exact hstep

end RUXt
