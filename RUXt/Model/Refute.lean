/-
Port of `theories/model/refute.v`: the refutation algorithm and the inadequacy
theorem.
-/
import RUXt.Lang.Semantics
import RUXt.Model.Logic
import RUXt.Model.Summary

namespace RUXt

open scoped RUXt.PMap

/-! ### Libraries -/

/-- `library` (`mk_library`). -/
structure Library where
  impls : ImplCtx
  types : SignCtx

/-! ### Bindings and derivable postconditions -/

/-- `bindings`. -/
def bindings (xs : List String) (es : List Expr) (e : Expr) : Expr :=
  (xs.zip es).foldr (fun xe e => .letIn (.named xe.1) xe.2 e) e

/-- `derivable_post`: well-typed states that can be derived by some UX logic. -/
def DerivablePost (isSafe : List Tid → List Val → Asrt → List Expr → Prop)
    (Λ : Library) (τ : Tid) (ε : Exit) (Q : Asrt) (e : Expr) : Prop :=
  -- Some function `f` outputs values of type `τ`
  ∃ f τs, Λ.types f = some ⟨τs, τ⟩ ∧
  -- Programs `es` generate values `vs` and precondition `P`
  ∃ vs P es, isSafe τs vs P es ∧
  -- `ε : Q` is a postcondition obtained from executing `f`
  ∃ L : Logic, L.DerivableSpec Λ.impls (.call f (Term.ofVals vs)) P Q ε ∧
  -- `e` is a witness program that calls `f` on the values returned by `es`
  ∃ xs, e = bindings xs es (.call f (Term.ofVars xs)) ∧ xs.length = es.length ∧ xs.Nodup

/-! ### Safe contexts -/

/-- `valid_type`. -/
def ValidType (v : Val) (τ : Tid) : Prop :=
  match τ with
  | .base k => v.baseType = k
  | .custom _ => True

/-- `wf_context`. -/
inductive WfContext (S : SummCtx) : List Tid → List Val → Asrt → List Expr → Prop
  | emp :
      WfContext S [] [] .emp []
  | star {τs : List Tid} {vs : List Val} {P : Asrt} {es : List Expr} {τ : Tid} {v : Val}
      {ς : Summary} :
      WfContext S τs vs P es →
      ς ∈ S τ → ValidType v τ → sat ((ς v).post ∗ P) →
      WfContext S (τ :: τs) (v :: vs) ((ς v).post ∗ P) ((ς v).src :: es)

/-- `safe_context`. -/
def SafeContext (S : SummCtx) (τs : List Tid) (vs : List Val) (P : Asrt)
    (es : List Expr) : Prop :=
  WfContext S τs vs P es

/-! ### The refutation procedure -/

/-- `try_refute`. -/
def TryRefute (Λ : Library) (S : SummCtx) : SummCtx ⊕ Expr → Prop
  -- The summary context `S` is updated to `S'`
  | .inl S' =>
      -- A new summary `Qf` is learned for `τ` with witness `ef` (`λQ`/`λe`)
      ∃ (τ : Tid) (Qf : Val → Asrt) (ef : Val → Expr),
        S' = SummCtx.update (fun v => ⟨Qf v, ef v⟩) τ S ∧
        -- `Qf` is a satisfiable post for some value `v`
        satPost Qf ∧
        -- Every `v` is a reachable safe value (`FALSE` is vacuously reachable)
        ∀ v, DerivablePost (SafeContext S) Λ τ (.ok v) (Qf v) (ef v)
  -- Found witness `e` for type unsoundness
  | .inr e =>
      -- Unsuccessful termination is derivable with a satisfiable post
      ∃ τ ε Q, DerivablePost (SafeContext S) Λ τ ε Q e ∧ sat Q ∧ ¬ ∃ v, ε = .ok v

/-- `wf_summ_ctx`. -/
inductive WfSummCtx (Λ : Library) : SummCtx → Prop
  | nil :
      WfSummCtx Λ baseSummCtx
  | cons {S S' : SummCtx} :
      WfSummCtx Λ S → TryRefute Λ S (.inl S') →
      WfSummCtx Λ S'

/-! ### Semantic interpretation of valid contexts -/

/-- `zip_expr`. -/
def zipExpr (S : List (Tid × Summary)) (vs : List Val) : List Expr :=
  (List.zipWith (fun v ς => ς v) vs (S.map Prod.snd)).map ConcreteSummary.src

/-- `zip_asrt`. -/
def zipAsrt (S : List (Tid × Summary)) (vs : List Val) : Asrt :=
  Asrt.iter ((List.zipWith (fun v ς => ς v) vs (S.map Prod.snd)).map ConcreteSummary.post) id

/-- `valid_types`. -/
def ValidTypes (S : List (Tid × Summary)) (vs : List Val) : Prop :=
  List.Forall₂ ValidType vs (S.map Prod.fst)

/-- `valid_context`: a context is valid if it is well-formed and the types are
valid. -/
def ValidContext (S : SummCtx) (τs : List Tid) (vs : List Val) (P : Asrt)
    (es : List Expr) : Prop :=
  ∃ S' : List (Tid × Summary), (∀ τς ∈ S', τς ∈ flatSummCtx S) ∧
    τs = S'.map Prod.fst ∧ es = zipExpr S' vs ∧ P = zipAsrt S' vs ∧
    sat P ∧ vs.length = S'.length ∧ ValidTypes S' vs

/-- `context_soundness`. -/
theorem context_soundness {S : SummCtx} {τs : List Tid} {vs : List Val} {P : Asrt}
    {es : List Expr} (hinput : WfContext S τs vs P es) :
    ValidContext S τs vs P es := by
  induction hinput with
  | emp => exact ⟨[], by simp, rfl, rfl, rfl, ⟨∅, rfl⟩, rfl, List.Forall₂.nil⟩
  | @star τs vs P es τ v ς _ hς hvalid hsat ih =>
    obtain ⟨S', hsub, rfl, rfl, rfl, hsat', hlen, hval⟩ := ih
    refine ⟨(τ, ς) :: S', ?_, rfl, rfl, rfl, hsat, by simp [hlen], .cons hvalid hval⟩
    intro τς hτς
    rcases List.mem_cons.mp hτς with rfl | h
    · exact hς
    · exact hsub _ h

/-! ### Summaries are reachable from some main program -/

/-- `reachable_from_program`. -/
def ReachableFromProgram (𝕍 : VarCtx) (xs : List String) (vs : List Val) (P : Asrt)
    (Λ : Library) (τ : Tid) (ε : Exit) (Q : Asrt) (e : Expr) : Prop :=
  safeProgram 𝕍 Λ.types e = some τ ∧
  UXFrameTriple Λ.impls (e.substs xs (Term.ofVals vs)) P Q ε

/-- `reachable_from_main`. -/
abbrev ReachableFromMain : Library → Tid → Exit → Asrt → Expr → Prop :=
  ReachableFromProgram ∅ [] [] .emp

/-- `valid_summ_ctx`: semantic interpretation of valid summaries. -/
def ValidSummCtx (Λ : Library) (S : SummCtx) : Prop :=
  ∀ τ ς, ς ∈ S τ → satPost (ConcreteSummary.post ∘ ς) ∧
    ∀ v, ValidType v τ → ReachableFromMain Λ τ (.ok v) ((ς v).post) ((ς v).src)

private theorem zipAsrt_append (S₁ : List (Tid × Summary)) (ςp : Tid × Summary)
    (vs₁ : List Val) (v : Val) (hlen : vs₁.length = S₁.length) :
    zipAsrt (S₁ ++ [ςp]) (vs₁ ++ [v])
      = Asrt.iter
          ((List.zipWith (fun v ς => ς v) vs₁ (S₁.map Prod.snd)).map ConcreteSummary.post
            ++ [(ςp.2 v).post]) id := by
  unfold zipAsrt
  rw [List.map_append, List.zipWith_append (by simpa using hlen), List.map_append]
  rfl

/-- The inductive core of `reachable_bindings`, stated with the variable
contexts in reversed form (as in the Rocq proof). -/
private theorem reachable_bindings_rev {Λ : Library} {S : SummCtx} {τ : Tid} {ε : Exit}
    {Q : Asrt} (hsumm : ValidSummCtx Λ S) :
    ∀ (S₂ : List (Tid × Summary)) (xs₂ : List String) (vs₂ : List Val)
      (S₁ : List (Tid × Summary)) (xs₁ : List String) (vs₁ : List Val) (e : Expr),
      (∀ τς ∈ S₁ ++ S₂, τς ∈ flatSummCtx S) →
      (xs₁ ++ xs₂).Nodup → ValidTypes S₂ vs₂ →
      xs₁.length = S₁.length → xs₂.length = S₂.length →
      vs₁.length = S₁.length → vs₂.length = S₂.length →
      ReachableFromProgram
        (consVarCtx (xs₁ ++ xs₂).reverse (((S₁ ++ S₂).map Prod.fst).reverse))
        (xs₁ ++ xs₂) (vs₁ ++ vs₂) (zipAsrt (S₁ ++ S₂) (vs₁ ++ vs₂)) Λ τ ε Q e →
      ReachableFromProgram (consVarCtx xs₁.reverse ((S₁.map Prod.fst).reverse))
        xs₁ vs₁ (zipAsrt S₁ vs₁) Λ τ ε Q (bindings xs₂ (zipExpr S₂ vs₂) e) := by
  intro S₂
  induction S₂ with
  | nil =>
    intro xs₂ vs₂ S₁ xs₁ vs₁ e _ _ _ _ hlenx₂ _ hlenv₂ hreach
    obtain rfl : xs₂ = [] := List.length_eq_zero_iff.mp (by simpa using hlenx₂)
    obtain rfl : vs₂ = [] := List.length_eq_zero_iff.mp (by simpa using hlenv₂)
    simpa using hreach
  | cons ςp S₂' ih =>
    intro xs₂ vs₂ S₁ xs₁ vs₁ e hsub hdup hval hlenx₁ hlenx₂ hlenv₁ hlenv₂ hreach
    obtain ⟨x, xs₂', rfl⟩ : ∃ y l, xs₂ = y :: l := by
      cases xs₂ with
      | nil => simp at hlenx₂
      | cons y l => exact ⟨y, l, rfl⟩
    obtain ⟨v, vs₂', rfl⟩ : ∃ w l, vs₂ = w :: l := by
      cases vs₂ with
      | nil => simp at hlenv₂
      | cons w l => exact ⟨w, l, rfl⟩
    -- Facts about the new head binding
    have hςmem : ςp.2 ∈ S ςp.1 := hsub ςp (by simp)
    obtain ⟨hv, hval'⟩ := List.forall₂_cons.mp hval
    obtain ⟨-, hreachv⟩ := hsumm ςp.1 ςp.2 hςmem
    obtain ⟨hsafe', hux'⟩ := hreachv v hv
    have hx_xs₁ : x ∉ xs₁ := by
      intro hmem
      exact (List.nodup_append.mp hdup).2.2 x hmem x List.mem_cons_self rfl
    -- The induction hypothesis, with the head moved to the end of the prefix
    have hdup' : ((xs₁ ++ [x]) ++ xs₂').Nodup := by simpa using hdup
    have hreach' : ReachableFromProgram (consVarCtx ((xs₁ ++ [x]) ++ xs₂').reverse
        ((((S₁ ++ [ςp]) ++ S₂').map Prod.fst).reverse)) ((xs₁ ++ [x]) ++ xs₂')
        ((vs₁ ++ [v]) ++ vs₂') (zipAsrt ((S₁ ++ [ςp]) ++ S₂') ((vs₁ ++ [v]) ++ vs₂'))
        Λ τ ε Q e := by
      simpa using hreach
    obtain ⟨hsafe, hux⟩ := ih xs₂' vs₂' (S₁ ++ [ςp]) (xs₁ ++ [x]) (vs₁ ++ [v]) e
      (by intro τς hτς; apply hsub; simp at hτς ⊢; tauto)
      hdup' hval'
      (by simp [hlenx₁]) (by simpa using hlenx₂)
      (by simp [hlenv₁]) (by simpa using hlenv₂)
      hreach'
    have hctx_eq : consVarCtx ((xs₁ ++ [x]).reverse) (((S₁ ++ [ςp]).map Prod.fst).reverse)
        = (consVarCtx xs₁.reverse ((S₁.map Prod.fst).reverse)).insert x ςp.1 := by
      rw [List.reverse_append, List.map_append, List.reverse_append]
      rfl
    constructor
    · -- the binding-extended program is safe
      show safeProgram _ Λ.types (.letIn (.named x) (ςp.2 v).src
        (bindings xs₂' (zipExpr S₂' vs₂') e)) = some τ
      have hsrc : safeProgram (consVarCtx xs₁.reverse ((S₁.map Prod.fst).reverse))
          Λ.types (ςp.2 v).src = some ςp.1 := safeMain_some _ hsafe'
      simp only [safeProgram, hsrc]
      rw [← hctx_eq]
      exact hsafe
    · -- the binding-extended program reaches the same state
      show UXFrameTriple Λ.impls ((Expr.letIn (.named x) (ςp.2 v).src
          (bindings xs₂' (zipExpr S₂' vs₂') e)).substs xs₁ (Term.ofVals vs₁))
        (zipAsrt S₁ vs₁) Q ε
      rw [Expr.substs_letIn (hlenx₁.trans hlenv₁.symm) hx_xs₁ (safeMain_closed hsafe')]
      refine let_spec (R := zipAsrt (S₁ ++ [ςp]) (vs₁ ++ [v])) (v := v) ?_ ?_
      · rw [zipAsrt_append S₁ ςp vs₁ v hlenv₁]
        exact frame_app_spec _ hux'
      · rw [Expr.substs_snoc _ x v (hlenx₁.trans hlenv₁.symm)]
        exact hux

/-- `reachable_bindings`. -/
theorem reachable_bindings {Λ : Library} {S : SummCtx}
    {S₁ S₂ : List (Tid × Summary)} {xs₁ xs₂ : List String} {vs₁ vs₂ : List Val}
    {τ : Tid} {ε : Exit} {Q : Asrt} {e : Expr}
    (hsumm : ValidSummCtx Λ S) (hsub : ∀ τς ∈ S₁ ++ S₂, τς ∈ flatSummCtx S)
    (hdup : (xs₁ ++ xs₂).Nodup) (hval : ValidTypes S₂ vs₂)
    (hlenx₁ : xs₁.length = S₁.length) (hlenx₂ : xs₂.length = S₂.length)
    (hlenv₁ : vs₁.length = S₁.length) (hlenv₂ : vs₂.length = S₂.length)
    (hreach : ReachableFromProgram
      (consVarCtx (xs₁ ++ xs₂) ((S₁ ++ S₂).map Prod.fst)) (xs₁ ++ xs₂) (vs₁ ++ vs₂)
      (zipAsrt (S₁ ++ S₂) (vs₁ ++ vs₂)) Λ τ ε Q e) :
    ReachableFromProgram
      (consVarCtx xs₁ (S₁.map Prod.fst)) xs₁ vs₁
      (zipAsrt S₁ vs₁) Λ τ ε Q (bindings xs₂ (zipExpr S₂ vs₂) e) := by
  have h₁ : consVarCtx xs₁ (S₁.map Prod.fst)
      = consVarCtx xs₁.reverse ((S₁.map Prod.fst).reverse) :=
    reverse_var_ctx (by simpa using hlenx₁) (List.nodup_append.mp hdup).1
  have h₂ : consVarCtx (xs₁ ++ xs₂) ((S₁ ++ S₂).map Prod.fst)
      = consVarCtx (xs₁ ++ xs₂).reverse (((S₁ ++ S₂).map Prod.fst).reverse) :=
    reverse_var_ctx (by simp [hlenx₁, hlenx₂]) hdup
  rw [h₁]
  exact reachable_bindings_rev hsumm _ _ _ _ _ _ _ hsub hdup hval
    hlenx₁ hlenx₂ hlenv₁ hlenv₂ (h₂ ▸ hreach)

/-- `derivable_for_main`. -/
theorem derivable_for_main {Λ : Library} {S : SummCtx} {e : Expr} {τ : Tid} {Q : Asrt}
    {ε : Exit} (hsumm : ValidSummCtx Λ S)
    (hpost : DerivablePost (SafeContext S) Λ τ ε Q e) :
    ReachableFromMain Λ τ ε Q e := by
  obtain ⟨f, τs, htype, vs, P, es, hctx, L, hspec, xs, rfl, hlenx, hdup⟩ := hpost
  obtain ⟨S', hsub, rfl, rfl, rfl, -, hlenv, hval⟩ := context_soundness hctx
  have hux := L.ux_frame_soundness hspec
  have hlenx' : xs.length = S'.length := by
    rw [hlenx]
    simp [zipExpr, hlenv]
  have hlenxv : xs.length = vs.length := hlenx'.trans hlenv.symm
  apply reachable_bindings (S₁ := []) (xs₁ := []) (vs₁ := []) hsumm
    (by simpa using hsub) (by simpa using hdup) hval rfl hlenx' rfl hlenv
  constructor
  · exact safe_call (by simpa using hlenx') hdup htype
  · show UXFrameTriple Λ.impls
      ((Expr.call f (Term.ofVars xs)).substs xs (Term.ofVals vs)) _ Q ε
    rw [Expr.substs_call hlenxv hdup]
    exact hux

/-- `summ_ctx_soundness`. -/
theorem summ_ctx_soundness {Λ : Library} {S : SummCtx} (hsumm : WfSummCtx Λ S) :
    ValidSummCtx Λ S := by
  induction hsumm with
  | nil =>
    intro τ ς hin
    cases τ with
    | base kind =>
      rw [baseSummCtx_base] at hin
      obtain rfl := List.mem_singleton.mp hin
      refine ⟨valPost_sat kind, ?_⟩
      intro v hv
      simp only [ValidType] at hv
      subst hv
      exact ⟨rfl, pure_val_spec _ v⟩
    | custom n =>
      rw [baseSummCtx_custom] at hin
      simp at hin
  | @cons S₀ S' _ hrefute ih =>
    intro τ' ς' hin
    simp only [TryRefute] at hrefute
    obtain ⟨τ, Qf, ef, rfl, ⟨v, hsat⟩, hpost⟩ := hrefute
    by_cases hττ' : τ = τ'
    · subst hττ'
      rw [SummCtx.update_apply] at hin
      rcases List.mem_cons.mp hin with rfl | hin'
      · exact ⟨⟨v, hsat⟩, fun v' _ => derivable_for_main ih (hpost v')⟩
      · exact ih τ ς' hin'
    · rw [SummCtx.update_apply_ne _ _ hττ'] at hin
      exact ih τ' ς' hin

/-! ### Inadequacy -/

/-- `has_refuted_type`: a type assignment in the library can be refuted. -/
def HasRefutedType (Λ : Library) (e : Expr) : Prop :=
  ∃ S, WfSummCtx Λ S ∧ TryRefute Λ S (.inr e)

/-- `inadequate`: a main program exhibits undefined behaviour. -/
def Inadequate (Λ : Library) (e : Expr) : Prop :=
  ∃ h, (Λ.impls ⊢ ⟨∅ | e⟩ ⇓ ⟨h | .err⟩) ∧ ∃ τ, safeMain Λ.types e = some τ

/-- Adequacy result for refuted type assignments (`inadequacy`). -/
theorem inadequacy {Λ : Library} {e : Expr} (hrefuted : HasRefutedType Λ e) :
    Inadequate Λ e := by
  obtain ⟨S, hctx, hrefute⟩ := hrefuted
  have hsumm := summ_ctx_soundness hctx
  simp only [TryRefute] at hrefute
  obtain ⟨τ, ε, Q, hpost, hsat, hε⟩ := hrefute
  obtain ⟨hsafe, hux⟩ := derivable_for_main hsumm hpost
  have hux' := ux_triple_preservation hux
  obtain ⟨h', hQ⟩ := hsat
  obtain ⟨h₀, hemp, hstep⟩ := hux' h' hQ
  obtain rfl : h₀ = ∅ := hemp
  refine ⟨h', ?_, τ, hsafe⟩
  cases ε with
  | ok v => exact absurd ⟨v, rfl⟩ hε
  | err => exact hstep
  | miss l => exact hstep

end RUXt
