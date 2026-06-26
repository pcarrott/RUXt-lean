import RUXt.Model.Summary

namespace RUXt

/-! ### Witness programs -/

/-- Binds each summary in `ςs` to a variable in `xs` and calls `f` on `xs`. -/
def witness (f : Fid) (xs : List PVar) (ςs : SummPicks) : Tele.triple ςs -t> Expr :=
  mergeSrcs xs ςs (.call f (Term.ofVars xs))

/-- A call to `f` on summaries `ςs` yields post `[ε:Φ]`. -/
def DerivableCall (Λ : Library) (f : Fid) (ςs : SummPicks)
    (ε : LExit) (Φ : Val → Tele.triple ςs -t> Asrt) : Prop :=
  ∃ L : Logic, L.DerivableSpec Λ
        ⟨mergePosts ςs, (mergeVals ςs).map (fun vs => .call f (Term.ofVals vs)), ε, Φ⟩

/-! ### Type safety of witnesses -/

private theorem mergeSrcs_safeProgram {Λ : Library} {ςs : SummPicks}
    {𝕍 : VarCtx} {call : Expr} {τ : Ty} {args : TeleArg (Tele.triple ςs)}
    {xs : List PVar} (Hlen : ςs.length = xs.length)
    (hsafe : ∀ τ ς, (τ, ς) ∈ ςs → ∀ args, SafeMain Λ (ς.src.apply args) τ)
    (hcall : SafeProgram (𝕍.consFrom xs (ςs.map Prod.fst)) Λ call τ) :
    SafeProgram 𝕍 Λ ((mergeSrcs xs ςs call).apply args) τ := by
  revert xs 𝕍
  induction' ςs with ς ςs ih
  · intro 𝕍 xs hlen hcall
    obtain rfl := by simpa using hlen.symm
    exact hcall
  · intro 𝕍 xs hlen hcall
    rcases xs with _ | ⟨x, xs⟩; contradiction
    rcases args with ⟨v, rest⟩
    rw [mergeSrcs_cons]; simp [SafeProgram]
    refine ⟨ς.1, hsafe _ _ (by simp) _, ?_⟩
    exact ih (by simp_all) (by simpa using hlen) hcall

/-- Witness programs are safe main programs. -/
theorem witness_safeMain {Λ : Library} {S : SummCtx} {ςs : SummPicks}
    {args : TeleArg (Tele.triple ςs)} {f : Fid} {params : List (PVar × Ty)}
    {body : Expr} {τ : Ty} {hdup : (params.map Prod.fst).Nodup}
    (hsumm : ValidSummCtx Λ S) (hsub : S [⊐] ςs)
    (himpl : Λ.MapsTo f ⟨params, body, τ, hdup⟩)
    (htypes : ςs.map Prod.fst = params.map Prod.snd) :
    SafeMain Λ ((witness f (params.map Prod.fst) ςs).apply args) τ := by
  have hlen : ςs.length = (params.map Prod.fst).length := by
    simpa using congrArg List.length htypes
  obtain hsafe := fun τ ς h => (hsumm τ ς (hsub τ ς h)).1.1
  refine mergeSrcs_safeProgram hlen hsafe ?_
  rw [htypes, consVarCtx_eq_rev hdup]
  exact safe_call himpl

/-! ### Semantics of witnesses -/

private theorem mergeSrcs_subst_nin {xs : List PVar} {ςs : SummPicks}
    (hclosed : ∀ τ ς, (τ, ς) ∈ ςs → ∀ args, (ς.src.apply args).ClosedProgram)
    {x : PVar} (hnin : x ∉ xs) {body : Expr} {v : Val} {args : TeleArg (Tele.triple ςs)}:
    ((mergeSrcs xs ςs body).apply args).subst (.named x) v
      = (mergeSrcs xs ςs (body.subst (.named x) v)).apply args := by
  revert xs
  induction' ςs with ς ςs ih
  · simp
  · intro xs hnin
    rcases ς with ⟨τ, ς⟩
    rcases args with ⟨_, rest⟩
    simp [mergeSrcs_cons, Expr.subst, Expr.substTerm]
    refine ⟨Expr.Closed.subst_eq (hclosed τ ς (by simp) _) _ (by tauto), ?_⟩
    cases xs
    · exact ih (fun τ ς h => hclosed τ ς (List.mem_cons_of_mem _ h)) (by tauto)
    · simp at hnin; simp [if_neg (Ne.symm hnin.1)]
      exact ih (fun τ ς h => hclosed τ ς (List.mem_cons_of_mem _ h)) hnin.2

open scoped PFun

private theorem witness_frame_step {Λ : Library} {ςs : SummPicks}
    (hreach : ∀ τ ς, (τ, ς) ∈ ςs → ReachableFromMain Λ τ ς.src .lok ς.post)
    {xs : List PVar} (hdup : xs.Nodup)
    (hlen : xs.length = ςs.length)
    {hF h h' : Heap} (hdisj : hF ##ₘ h)
    {args : TeleArg (Tele.triple ςs)} (hpre: HProp h ((mergePosts ςs).apply args))
    {body : Expr} {εₛ : Exit}
    (hstep : Λ ⊢ ⟨hF ∪ h | body.substs xs (
        Term.ofVals ((mergeVals ςs).apply args)
    )⟩ ⇓ᵢ ⟨h' | εₛ⟩) :
     Λ ⊢ ⟨hF | (mergeSrcs xs ςs body).apply args⟩ ⇓ᵢ ⟨h' | εₛ⟩ := by
  revert body args xs hF h h'
  induction' ςs with ς ςs ih
  · simp_all
  · intro xs hdup hlen hF h h' hdisjF args hpre body hstep
    rcases xs with _ | ⟨x, xs⟩; contradiction
    rcases args with ⟨v, rest⟩
    rw [mergeSrcs_cons]
    rw [mergePosts_cons] at hpre
    obtain ⟨h1, h2, rfl, hdisj, hpre1, hpre2⟩ := hpre
    obtain ⟨hdisjF1, hdisjF2⟩ := PFun.disjoint_union_r.1 hdisjF
    rw [← PFun.union_assoc, mergeVals_cons] at hstep
    obtain ⟨_, hux⟩ := hreach ς.1 ς.2 (by simp)
    obtain ⟨h, hemp, εₛ, hε, hstep1⟩ := hux rest.fst v h1 hpre1
    injection hε with hε; subst hε
    simp [teleBind_apply] at hemp; subst hemp
    rcases frame_addition hstep1 hF hdisjF1.symm with ⟨hstep1, _⟩ | ⟨l, Heq, _⟩
    · simp_all; refine FrameStep.letIn hstep1 ?_
      obtain hclosed := fun τ ς h args => safeMain_closed ((hreach τ ς (Or.inr h)).1 args)
      rw [mergeSrcs_subst_nin hclosed hdup.1, PFun.union_comm hdisjF1.symm]
      exact ih hdup.2 hlen (PFun.disjoint_union_l.2 ⟨hdisjF2, hdisj⟩) hpre2 hstep
    · contradiction

/-- Witness programs exhibit the same behaviour as a function call on the summaries. -/
theorem witness_triple {Λ : Library} {S : SummCtx} {ςs : SummPicks}
    {f : Fid} {xs : List PVar} {ε : LExit} {Φ : Val → Tele.triple ςs -t> Asrt}
    (hsumm : ValidSummCtx Λ S) (hsub : S [⊐] ςs)
    (hdup : xs.Nodup) (hlen : xs.length = ςs.length)
    (hcall : DerivableCall Λ f ςs ε Φ) :
    UXFrameTriple Λ (teleBind fun _ ↦ Asrt.emp, witness f xs ςs, ε, Φ) := by
  intro args r h' hQ; rw [teleBind_apply]
  obtain ⟨L, hspec⟩ := hcall
  obtain ⟨h, hpre, εₛ, hε, hstep⟩ := L.ux_frame_soundness hspec args r h' hQ
  rw [teleMap_apply] at hstep
  refine ⟨∅, rfl, εₛ, hε, ?_⟩
  obtain hreach := fun τ ς h => (hsumm τ ς (hsub τ ς h)).1
  refine witness_frame_step hreach hdup hlen (PFun.disjoint_empty_l h) hpre ?_
  rw [PFun.empty_union, Expr.substs_call (by rw [mergeVals_length]; exact hlen) hdup]
  exact hstep
