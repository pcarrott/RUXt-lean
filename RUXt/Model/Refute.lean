import RUXt.Model.Witness

namespace RUXt

/-! ### The type refutation algorithm -/

/-- Well-typed states that can be derived by some UX logic. -/
def DerivablePost (Λ : Library) (ςs : SummPicks) (f : Fid) (xs : List PVar)
    (τ : Ty) (ε : LExit) (Φ : Val → Tele.triple ςs -t> Asrt) : Prop :=
      -- Some function `f` outputs values of type `τ`
      ∃ params body hdup, Λ.MapsTo f ⟨params, body, τ, hdup⟩ ∧
      -- The concrete input types must match the types in `ςs`
      xs = params.map Prod.fst ∧ ςs.map Prod.fst = params.map Prod.snd ∧
      -- `[ε : Φ]` is obtained from executing `f` after composing the summaries in `ςs`
      DerivableCall Λ f ςs ε Φ

/-- The refutation procedure. -/
def TryRefute (Λ : Library) (S : SummCtx) (r : SummCtx ⊕ Expr) : Prop :=
  -- Pick a subset ςs of Σ, for input summaries
  ∃ ςs, S [⊐] ςs ∧
  -- Construct [e : τ] that terminates with postcondition [ε : Φ]
  ∃ f xs τ ε Φ, DerivablePost Λ ςs f xs τ ε Φ ∧
  -- The postcondition is satisfiable
  ∃ v args, Sat ((Φ v).apply args) ∧
  -- Case analysis on whether the derived state is Ok
  match r with
  | .inl S' => ε = .lok ∧ -- Case Ok: The summary context Σ is updated to Σ'
        S' = SummCtx.update S τ ⟨Tele.triple ςs, Φ, witness f xs ςs⟩
  -- Found witness `e` for type unsoundness
  | .inr e => ε ≠ .lok ∧ --Cases Err/Miss: Found witness e for type unsoundness
      e = (witness f xs ςs).apply args

/-- Meta-loop for deriving well-formed contexts. -/
inductive WfSummCtx (Λ : Library) : SummCtx → Prop
  | nil :
      WfSummCtx Λ baseSummCtx
  | cons {S S' : SummCtx} :
      WfSummCtx Λ S → TryRefute Λ S (.inl S') →
      WfSummCtx Λ S'

/-! ### Inference soundness -/

/-- Any derivable state can be witnessed by a main program. -/
theorem derivable_for_main {Λ : Library} {S : SummCtx} {ςs : SummPicks} {f : Fid}
    {xs : List PVar} {τ : Ty} {ε : LExit} {Q : Val → Tele.triple ςs -t> Asrt}
    (hsumm : ValidSummCtx Λ S) (hsub : S [⊐] ςs)
    (hpost : DerivablePost Λ ςs f xs τ ε Q) :
    ReachableFromMain Λ τ (witness f xs ςs) ε Q := by
  obtain ⟨params, _, hdup, himpl, rfl, htypes, L, hspec⟩ := hpost
  refine ⟨fun _ => witness_safeMain hsumm hsub himpl htypes, ?_⟩
  refine witness_triple hsumm hsub hdup ?_ ⟨L, hspec⟩
  simpa using congrArg List.length htypes.symm

/-- Soundness of well-formed type summary contexts. -/
theorem summCtx_soundness {Λ : Library} {S : SummCtx}
    (hsumm : WfSummCtx Λ S) : ValidSummCtx Λ S := by
  induction hsumm with
  | nil =>
    intro τ ς hin
    rcases τ with ⟨kind⟩
    · rw [baseSummCtx_base hin]
      exact baseSummary_valid Λ kind
    · contradiction
  | cons _ hrefute ih =>
    intro τ' ς' hin
    obtain ⟨ςs, hsub, f, xs, τ, ε, Φ, hpost, v, args, hsat, ⟨rfl, rfl⟩⟩ := hrefute
    rcases SummCtx.mem_update hin with ⟨rfl, rfl⟩ | hin
    · exact ⟨derivable_for_main ih hsub hpost, v, args, hsat⟩
    · exact ih τ' ς' hin

/-! ### Soundness result of RUXt -/

/-- A type assignment in the library can be refuted. -/
def HasRefutedType (Λ : Library) (e : Expr) : Prop :=
  ∃ S, WfSummCtx Λ S ∧ TryRefute Λ S (.inr e)
/-- A main program exhibits undefined behaviour. -/
def Inadequate (Λ : Library) (e : Expr) : Prop :=
  ∃ h, (Λ ⊢ ⟨∅ | e⟩ ⇓ ⟨h | .err⟩) ∧ ∃ τ, SafeMain Λ e τ

/-- Adequacy result for refuted type assignments. -/
theorem inadequacy {Λ : Library} {e : Expr}
    (hrefuted : HasRefutedType Λ e) : Inadequate Λ e := by
  obtain ⟨S, hctx, hrefute⟩ := hrefuted
  obtain hctx := summCtx_soundness hctx
  obtain ⟨ςs, hsub, f, xs, τ, εₗ, Φ, hpost, r, args, ⟨h', hΦ⟩, ⟨Hnok, rfl⟩⟩ := hrefute
  obtain ⟨hsafe, hux⟩ := derivable_for_main hctx hsub hpost
  refine ⟨h', ?_, τ, hsafe args⟩
  obtain ⟨_, _, _, _, _, _, L, hspec⟩ := hpost
  obtain ⟨_, _, ε, ⟨hε, _⟩⟩ := L.ux_frame_soundness hspec _ _ _ hΦ
  obtain ⟨h, hP, hstep⟩ := ux_frame_triple_spec hux _ _ _ hΦ _ hε
  rw [teleBind_apply] at hP; rw [hP] at *
  rcases εₗ; contradiction
  · let .unit := r
    injection hε with hε; subst hε
    exact hstep
  · let .loc _ := r
    injection hε with hε; subst hε
    exact hstep

end RUXt
