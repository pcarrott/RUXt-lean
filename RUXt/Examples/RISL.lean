import RUXt.Model.Logic

namespace RUXt

/-! ### Function specifications -/

/-- A function specification is parameterised over an arbitrary telescope `tt`
together with a *value projection* `vals : tt -t> List Val`, which reads off,
for each instantiation of the telescope, the list of concrete argument values
with which the function is called. -/
def FunSpec : Type 1 := (tt : Tele.{0}) ×
  (tt -t> List Val) × (tt -t> Asrt.{0}) × LExit × (Val → tt -t> Asrt.{0})

/-- The exit tag of a function specification. -/
def FunSpec.exit : FunSpec → LExit
  | ⟨_, _, _, ε, _⟩ => ε

def SpecCtx := String → List FunSpec
instance : EmptyCollection SpecCtx := ⟨fun _ => []⟩

@[simp] theorem SpecCtx.empty_apply (f : String) : (∅ : SpecCtx) f = [] := rfl

/-- Specification context update. -/
def SpecCtx.update (s : FunSpec) (f : String) (Γ : SpecCtx) : SpecCtx :=
  Function.update Γ f (s :: Γ f)
/-- Specification context inclusion, `Γ [⊆] Γ'`. -/
def SpecCtx.Subseteq (Γ Γ' : SpecCtx) : Prop := ∀ f, Γ f ⊆ Γ' f
@[inherit_doc] scoped infix:50 " [⊆] " => SpecCtx.Subseteq

theorem SpecCtx.update_apply (Γ : SpecCtx) (f : String) (s : FunSpec) :
    Γ.update s f f = s :: Γ f :=
  Function.update_self ..
theorem SpecCtx.update_apply_ne (Γ : SpecCtx) {f g : String} (s : FunSpec) (h : f ≠ g) :
    Γ.update s f g = Γ g :=
  Function.update_of_ne (Ne.symm h) ..

/-! ### Triple notation -/

-- Notation for `WfSpec` where the precondition `P`, the program `e` and the
-- postcondition `Q` are supplied as telescoped functions directly:
-- `Γ ⊢ ⌈P⌉ e ⌈ε, Q⌉`.  The program `e` is parsed at maximal precedence, so an
-- applied `e` must be parenthesised; this both disambiguates the notation and
-- avoids a clash with Mathlib's ceiling notation `⌈·⌉`.
open Lean Parser Term in
scoped syntax:50 (name := wfSpecNotation) term:51 " ⊢ " "⌈" term "⌉ " term:max
  " ⌈" term ", " term "⌉" : term

-- Binder form of the `WfSpec` notation:
-- `Γ ⊢ λₗ args, ⌈P⌉ e ⌈ε : λₗ r, Q⌉`.
-- The telescope binders `args` are written once, immediately after `λₗ`, and are
-- shared by the precondition `P`, the program `e` and (together with the result
-- binder `r`) the postcondition `Q`, so they need not be repeated in each component
-- of the triple.  The telescope itself is synthesised from `args`.  As above, `e`
-- is parsed at maximal precedence.
open Lean Parser Term in
scoped syntax:50 (name := wfSpecBinderNotation) term:51 " ⊢ " "λₗ" (ppSpace funBinder)* ", "
  "⌈" term "⌉ " term:max " ⌈" term " : " "λₗ" ppSpace funBinder ", " term "⌉" : term

macro_rules
  | `($Γ ⊢ ⌈$P⌉ $e ⌈$ε, $Q⌉) => do
      let wf := Lean.mkIdent `RUXt.WfSpec
      `($wf $Γ ⟨$P, $e, $ε, $Q⟩)
  | `($Γ ⊢ λₗ $bs:funBinder*, ⌈$P⌉ $e ⌈$ε : λₗ $r, $Q⌉) => do
      let wf := Lean.mkIdent `RUXt.WfSpec
      let tl ← `([tele $bs*])
      if bs.isEmpty then
        `($wf $Γ (tt := $tl) ⟨$P, $e, $ε, fun $r => $Q⟩)
      else
        `($wf $Γ (tt := $tl) ⟨fun $bs* => $P, fun $bs* => $e, $ε, fun $r => fun $bs* => $Q⟩)

/-! ### The RISL proof rules  -/

/-- RISL triples, `Γ ⊢ ⌈P⌉ e ⌈ε, Q⌉`. -/
inductive WfSpec : SpecCtx → {tt : Tele} → SymTriple tt → Prop
  | pure {Γ : SpecCtx} :
      Γ ⊢ λₗ p, ⌈ .emp ⌉ (.pure p) ⌈ .lok : λₗ r, ⌞ some r = Pure.eval p ⌟ ⌉
  | assume {Γ : SpecCtx} :
      Γ ⊢ λₗ , ⌈ .emp ⌉ (.assume .true) ⌈ .lok : λₗ r, ⌞ r = .unit ⌟ ⌉
  | error {Γ : SpecCtx} :
      Γ ⊢ λₗ , ⌈ .emp ⌉ (.error) ⌈ .lerr : λₗ r, ⌞ r = .unit ⌟ ⌉
  | letIn {Γ : SpecCtx} {tt : Tele} {x : Binder} {e₁ e₂ : tt -t> Expr}
        {P : tt -t> Asrt} {ε : LExit} {Φ Φ' : Val → tt -t> Asrt} {v : Val} :
      (Γ ⊢ ⌈P⌉ e₁ ⌈.lok, Φ'⌉) →
      (Γ ⊢ ⌈Φ' v⌉ (e₂.map fun e => e.subst x v) ⌈ε, Φ⌉) →
      (Γ ⊢ ⌈P⌉ (teleBind fun args => .letIn x (e₁.apply args) (e₂.apply args)) ⌈ε, Φ⌉)
  | letCut {Γ : SpecCtx} {tt : Tele} {x : Binder} {e₁ e₂ : tt -t> Expr}
        {P : tt -t> Asrt} {ε : LExit} {Φ : Val → tt -t> Asrt} :
      (Γ ⊢ ⌈P⌉ e₁ ⌈ε, Φ⌉) → ε ≠ .lok →
      (Γ ⊢ ⌈P⌉ (teleBind fun args => .letIn x (e₁.apply args) (e₂.apply args)) ⌈ε, Φ⌉)
  | choice {Γ : SpecCtx} {tt : Tele} {eᵢ e₁ e₂ : tt -t> Expr}
        {P : tt -t> Asrt} {ε : LExit} {Φ : Val → tt -t> Asrt} :
      (eᵢ = e₁ ∨ eᵢ = e₂) → (Γ ⊢ ⌈P⌉ eᵢ ⌈ε, Φ⌉) →
      (Γ ⊢ ⌈P⌉ (teleBind fun args => .choice (e₁.apply args) (e₂.apply args)) ⌈ε, Φ⌉)
  | alloc {Γ : SpecCtx} :
      Γ ⊢ λₗ , ⌈ .emp ⌉ (.alloc (.int 1)) ⌈ .lok : λₗ r, .ex fun l => ⌞ r = .loc l ⌟ ∗ l ↦? ⌉
  | free {Γ : SpecCtx} :
      Γ ⊢ λₗ l v, ⌈ l ↦ v ⌉ (.free (.loc l)) ⌈ .lok : λₗ r, ⌞ r = .unit ⌟ ∗ l ↦∅ ⌉
  | freeUninit {Γ : SpecCtx} :
      Γ ⊢ λₗ l, ⌈ l ↦? ⌉ (.free (.loc l)) ⌈ .lok : λₗ r, ⌞ r = .unit ⌟ ∗ l ↦∅ ⌉
  | freeFreed {Γ : SpecCtx} :
      Γ ⊢ λₗ l, ⌈ l ↦∅ ⌉ (.free (.loc l)) ⌈ .lerr : λₗ r, ⌞ r = .unit ⌟ ∗ l ↦∅ ⌉
  | store {Γ : SpecCtx} :
      Γ ⊢ λₗ l v v', ⌈ l ↦ v' ⌉ (.store (.loc l) (.val v)) ⌈ .lok : λₗ r, ⌞ r = .unit ⌟ ∗ l ↦ v ⌉
  | storeUninit {Γ : SpecCtx} :
      Γ ⊢ λₗ l v, ⌈ l ↦? ⌉ (.store (.loc l) (.val v)) ⌈ .lok : λₗ r, ⌞ r = .unit ⌟ ∗ l ↦ v ⌉
  | storeFreed {Γ : SpecCtx} :
      Γ ⊢ λₗ l v, ⌈ l ↦∅ ⌉ (.store (.loc l) (.val v)) ⌈ .lerr : λₗ r, ⌞ r = .unit ⌟ ∗ l ↦∅ ⌉
  | load {Γ : SpecCtx} :
      Γ ⊢ λₗ l v, ⌈ l ↦ v ⌉ (.load (.loc l)) ⌈ .lok : λₗ r, ⌞ r = v ⌟ ∗ l ↦ v ⌉
  | loadUninit {Γ : SpecCtx} :
      Γ ⊢ λₗ l, ⌈ l ↦? ⌉ (.load (.loc l)) ⌈ .lerr : λₗ r, ⌞ r = .unit ⌟ ∗ l ↦? ⌉
  | loadFreed {Γ : SpecCtx} :
      Γ ⊢ λₗ l, ⌈ l ↦∅ ⌉ (.load (.loc l)) ⌈ .lerr : λₗ r, ⌞ r = .unit ⌟ ∗ l ↦∅ ⌉
  | frame {Γ : SpecCtx} {tt : Tele} {e : tt -t> Expr}
        {P R : tt -t> Asrt} {ε : LExit} {Φ : Val → tt -t> Asrt} :
      (Γ ⊢ ⌈P⌉ e ⌈ε, Φ⌉) →
      (Γ ⊢ ⌈teleBind fun args => P.apply args ∗ R.apply args⌉ e
        ⌈ε, fun v => teleBind fun args => (Φ v).apply args ∗ R.apply args⌉)
  | disj {Γ : SpecCtx} {tt : Tele} {e : tt -t> Expr}
        {P₁ P₂ : tt -t> Asrt} {ε : LExit} {Φ₁ Φ₂ : Val → tt -t> Asrt} :
      (Γ ⊢ ⌈P₁⌉ e ⌈ε, Φ₁⌉) → (Γ ⊢ ⌈P₂⌉ e ⌈ε, Φ₂⌉) →
      (Γ ⊢ ⌈teleBind fun args => P₁.apply args ∨ₕ P₂.apply args⌉ e
        ⌈ε, fun v => teleBind fun args => (Φ₁ v).apply args ∨ₕ (Φ₂ v).apply args⌉)
  | cons {Γ Γ' : SpecCtx} {tt tt' : Tele}
        {P : tt -t> Asrt} {e : tt -t> Expr} {Φ : Val → tt -t> Asrt}
        {P' : tt' -t> Asrt} {e' : tt' -t> Expr} {Φ' : Val → tt' -t> Asrt}
        {ε : LExit} (f : TeleArg tt → TeleArg tt') :
      Γ' [⊆] Γ →
      (∀ args, ⊨ (P'.apply (f args) →ₕ P.apply args)) →
      (∀ v args, ⊨ (Φ v).apply args →ₕ (Φ' v).apply (f args)) →
      (∀ args, e.apply args = e'.apply (f args)) →
      (Γ' ⊢ ⌈P'⌉ e' ⌈ε, Φ'⌉) →
      (Γ ⊢ ⌈P⌉ e ⌈ε, Φ⌉)
  | ex {Γ : SpecCtx} {tt : Tele} {X : Type} {e : tt -t> Expr}
        {P : tt -t> Asrt} {ε : LExit} {Φ : Val → tt -t> Asrt} :
      (Γ ⊢ ⌈P⌉ e ⌈ε, Φ⌉) →
      (Γ ⊢ ⌈teleBind fun args => .ex fun _ : X => P.apply args⌉ e
        ⌈ε, fun v => teleBind fun args => .ex fun _ : X => (Φ v).apply args⌉)
  | call {Γ : SpecCtx} {tt : Tele} {f : String} {vals : tt -t> List Val}
      {P : tt -t> Asrt} {ε : LExit} {Φ : Val → tt -t> Asrt} :
      (⟨tt, vals, P, ε, Φ⟩ : FunSpec) ∈ Γ f →
      (Γ ⊢ ⌈P⌉ (vals.map fun l => .call f (Term.ofVals l)) ⌈ε, Φ⌉)

/-- Re-index a derivation along a telescope map `f : TeleArg tt' → TeleArg tt`.
This is the special case of the (generalised) Consequence rule that only changes
the telescope, leaving the underlying assertions and program untouched (up to the
reindexing).  It is the standard way to instantiate a base rule — whose telescope
contains *exactly* its used variables. -/
theorem WfSpec.reindex {Γ : SpecCtx} {tt tt' : Tele} {e : tt -t> Expr}
    {P : tt -t> Asrt} {ε : LExit} {Φ : Val → tt -t> Asrt}
    (f : TeleArg tt' → TeleArg tt) (h : Γ ⊢ ⌈P⌉ e ⌈ε, Φ⌉) :
    Γ ⊢ ⌈teleBind fun args => P.apply (f args)⌉
        (teleBind fun args => e.apply (f args))
        ⌈ε, fun r => teleBind fun args => (Φ r).apply (f args)⌉ :=
  .cons f (fun _ => List.Subset.refl _)
    (fun args => by rw [teleBind_apply]; exact hImplies_refl _)
    (fun r args => by rw [teleBind_apply]; exact hImplies_refl _)
    (fun args => by rw [teleBind_apply])
    h

abbrev Expr.substSym (body : Expr) (xs : List (PVar × Ty))
    {tt : Tele} (vals : tt -t> List Val) : tt -t> Expr :=
  teleBind fun args => body.substs (xs.map Prod.fst) (Term.ofVals (vals.apply args))

/-- Well-formed specification contexts, `γ ≺ₛ Γ`. -/
inductive WfSpecCtx (Λ : Library) : SpecCtx → Prop
  | empty :
      WfSpecCtx Λ ∅
  | update {Γ Γ' : SpecCtx} {tt : Tele} {f xs body τ hdup}
      {vals : tt -t> List Val} {P ε Φ}  :
      WfSpecCtx Λ Γ → Γ' = Γ.update ⟨tt, vals, P, ε, Φ⟩ f →
      Λ.MapsTo f ⟨xs, body, τ, hdup⟩ →
        (Γ ⊢ ⌈P⌉ (body.substSym xs vals) ⌈ε, Φ⌉) →
      WfSpecCtx Λ Γ'
@[inherit_doc] scoped infix:50 " ≺ₛ " => WfSpecCtx

/-! ### Soundness of RISL -/

/-- The under-approximate call triple associated to a function specification. -/
def FunSpec.callTriple (f : String) : (s : FunSpec) → SymTriple s.1
  | ⟨_, vals, P, ε, Φ⟩ => ⟨P, vals.map (fun vs => .call f (Term.ofVals vs)), ε, Φ⟩

/-- A specification context *never mentions the `lmiss` exit tag*.  Contexts built
by `WfSpecCtx` enjoy this property, which is what makes the frame rule sound. -/
def SpecCtxNoMiss (Γ : SpecCtx) : Prop :=
  ∀ (f : String) (s : FunSpec), s ∈ Γ f → s.exit ≠ .lmiss

/-- A specification context is *semantically sound* when every stored
specification yields a valid under-approximate call triple. -/
def SoundSpecCtx (Λ : Library) (Γ : SpecCtx) : Prop :=
  ∀ (f : String) (s : FunSpec), s ∈ Γ f → UXFrameTriple Λ (s.callTriple f)

theorem SpecCtxNoMiss.mono {Γ Γ' : SpecCtx}
    (hsub : Γ' [⊆] Γ) (h : SpecCtxNoMiss Γ) : SpecCtxNoMiss Γ' :=
  fun f s hmem => h f s (hsub f hmem)

theorem SoundSpecCtx.mono {Λ : Library} {Γ Γ' : SpecCtx}
    (hsub : Γ' [⊆] Γ) (h : SoundSpecCtx Λ Γ) : SoundSpecCtx Λ Γ' :=
  fun f s hmem => h f s (hsub f hmem)

/-- No RISL derivation over a `lmiss`-free context ends in the `lmiss` tag. -/
theorem WfSpec.exit_ne_lmiss {Γ : SpecCtx} {tt : Tele} {triple : SymTriple tt}
    (h : WfSpec Γ triple) : SpecCtxNoMiss Γ → triple.exit ≠ .lmiss := by
  induction h <;> try tauto
  rename_i hsub _ _ _ _ hmiss
  exact fun h => hmiss (SpecCtxNoMiss.mono hsub h)

/-- A sound call triple can be recovered from a sound body triple. -/
theorem callTriple_of_body {Λ : Library} {f : String} {xs : List (PVar × Ty)}
    {body : Expr} {τ : Ty} {hdup} {tt : Tele}
    {vals : tt -t> List Val} {P : tt -t> Asrt} {ε : LExit} {Φ : Val → tt -t> Asrt}
    (hmaps : Λ.MapsTo f ⟨xs, body, τ, hdup⟩)
    (hbody : UXFrameTriple Λ ⟨P, body.substSym xs vals, ε, Φ⟩) :
    UXFrameTriple Λ ⟨P, vals.map (fun l => .call f (Term.ofVals l)), ε, Φ⟩ := by
  intro args v h' hΦ
  obtain ⟨h, hP, εₛ, hε, hstep⟩ := hbody args v h' hΦ
  rw [teleBind_apply] at hstep
  refine ⟨h, hP, εₛ, hε, ?_⟩
  rw [teleMap_apply]
  exact .call hmaps hstep

/-! #### Soundness of the individual structural proof rules -/

/-- Soundness of the sequencing rule `letIn`. -/
theorem uxframe_letIn {Λ : Library} {tt : Tele} {x : Binder} {e₁ e₂ : tt -t> Expr}
    {P : tt -t> Asrt} {ε : LExit} {Φ Φ' : Val → tt -t> Asrt} {v : Val}
    (h₁ : UXFrameTriple Λ ⟨P, e₁, .lok, Φ'⟩)
    (h₂ : UXFrameTriple Λ ⟨Φ' v, e₂.map fun e => e.subst x v, ε, Φ⟩) :
    UXFrameTriple Λ ⟨P, teleBind fun args =>
      .letIn x (e₁.apply args) (e₂.apply args), ε, Φ⟩ := by
  intro args r h' hΦ
  obtain ⟨h'', hΦ', ε₂, hε₂, hstep₂⟩ := h₂ args r h' hΦ
  obtain ⟨h, hP, ε₁, hε₁, hstep₁⟩ := h₁ args v h'' hΦ'
  cases hε₁
  simp_all [teleBind_apply, teleMap_apply]
  exact ⟨h, hP, .letIn hstep₁ hstep₂⟩

/-- Soundness of the short-circuiting sequencing rule `letCut`. -/
theorem uxframe_letCut {Λ : Library} {tt : Tele} {x : Binder} {e₁ e₂ : tt -t> Expr}
    {P : tt -t> Asrt} {ε : LExit} {Φ : Val → tt -t> Asrt}
    (h : UXFrameTriple Λ ⟨P, e₁, ε, Φ⟩) (hne : ε ≠ .lok) :
    UXFrameTriple Λ ⟨P, teleBind fun args =>
      .letIn x (e₁.apply args) (e₂.apply args), ε, Φ⟩ := by
  intro args r h' hΦ
  obtain ⟨h, hP, εₛ, hε, hstep⟩ := h args r h' hΦ
  simp [teleBind_apply]
  refine' ⟨h, hP, εₛ, hε, FrameStep.letCut hstep _⟩
  cases ε <;> cases r <;> simp_all [LExit.toExit]
  · intro x; subst hε; simp
  · intro x; subst hε; simp

/-- Soundness of the nondeterministic choice rule `choice`. -/
theorem uxframe_choice {Λ : Library} {tt : Tele} {eᵢ e₁ e₂ : tt -t> Expr}
    {P : tt -t> Asrt} {ε : LExit} {Φ : Val → tt -t> Asrt}
    (he : eᵢ = e₁ ∨ eᵢ = e₂) (h : UXFrameTriple Λ ⟨P, eᵢ, ε, Φ⟩) :
    UXFrameTriple Λ ⟨P, teleBind fun args =>
      (e₁.apply args).choice (e₂.apply args), ε, Φ⟩ := by
  intro args r h' hΦ
  obtain ⟨h, hP, εₛ, hε, hstep⟩ := h args r h' hΦ
  simp_all [teleBind_apply]
  rcases he with ⟨rfl⟩ | ⟨rfl⟩
  · exact ⟨h, hP, .choice hstep (Or.inl rfl)⟩;
  · exact ⟨h, hP, .choice hstep (Or.inr rfl)⟩

/-- Soundness of the frame rule.  This is where the `lmiss`-free assumption is needed: framing a `miss` outcome over a heap that owns the missed location is unsound, but such an outcome cannot occur since `ε ≠ lmiss`. -/
theorem uxframe_frame {Λ : Library} {tt : Tele} {R : tt -t> Asrt} {e : tt -t> Expr}
    {P : tt -t> Asrt} {ε : LExit} {Φ : Val → tt -t> Asrt}
    (hne : ε ≠ .lmiss)
    (h : UXFrameTriple Λ ⟨P, e, ε, Φ⟩) :
    UXFrameTriple Λ ⟨teleBind fun args => P.apply args ∗ R.apply args, e, ε,
      fun v => teleBind fun args => (Φ v).apply args ∗ R.apply args⟩ := by
  intro args v h' hΦ
  rw [teleBind_apply] at *
  obtain ⟨h₁, h₂, rfl, hdisj, ⟨hh₁, hh₂⟩⟩ := hΦ
  obtain ⟨h₁, hP, εₛ, hε, hstep⟩ := h args v h₁ hh₁
  obtain ⟨hstepF, hdisj⟩ | ⟨l, rfl, hdom⟩ := frame_addition hstep h₂ hdisj
  · exact ⟨h₁ ∪ h₂, ⟨h₁, h₂, rfl, hdisj, hP, hh₂⟩, εₛ, hε, hstepF⟩
  · cases ε <;> simp_all [LExit.toExit]
    cases v <;> cases hε

/-- Soundness of the disjunction rule. -/
theorem uxframe_disj {Λ : Library} {tt : Tele} {e : tt -t> Expr}
    {P₁ P₂ : tt -t> Asrt} {ε : LExit} {Φ₁ Φ₂ : Val → tt -t> Asrt}
    (h₁ : UXFrameTriple Λ ⟨P₁, e, ε, Φ₁⟩)
    (h₂ : UXFrameTriple Λ ⟨P₂, e, ε, Φ₂⟩) :
    UXFrameTriple Λ ⟨teleBind fun args => P₁.apply args ∨ₕ P₂.apply args, e, ε,
      fun v => teleBind fun args => (Φ₁ v).apply args ∨ₕ (Φ₂ v).apply args⟩ := by
  intro args v h' hΦ
  simp_all [teleBind_apply]
  rcases hΦ with ⟨hΦ₁⟩ | ⟨hΦ₂⟩
  · obtain ⟨h, hP₁, εₛ, hε, hstep⟩ := h₁ args v h' hΦ₁
    exact ⟨h, Or.inl hP₁, εₛ, hε, hstep⟩
  · obtain ⟨h, hP₂, εₛ, hε, hstep⟩ := h₂ args v h' hΦ₂
    exact ⟨h, Or.inr hP₂, εₛ, hε, hstep⟩

/-- Soundness of the existential rule. -/
theorem uxframe_ex {Λ : Library} {tt : Tele} {e : tt -t> Expr} {P : tt -t> Asrt}
    {ε : LExit} {Φ : Val → tt -t> Asrt} {X : Type}
    (h : UXFrameTriple Λ ⟨P, e, ε, Φ⟩) :
    UXFrameTriple Λ ⟨teleBind fun args => .ex fun _ : X => P.apply args, e, ε,
      fun v => teleBind fun args => .ex fun _ : X => (Φ v).apply args⟩ := by
  intro args v h' hΦ
  rw [teleBind_apply] at *
  obtain ⟨x, hx⟩ := hΦ
  obtain ⟨h, hh, εₛ, hε, hstep⟩ := h args v h' hx;
  exact ⟨h, ⟨x, hh⟩, εₛ, hε, hstep⟩

/-- Soundness of the (generalised) consequence rule. -/
theorem uxframe_cons {Λ : Library} {tt tt' : Tele} {e : tt -t> Expr} {e' : tt' -t> Expr}
    {P : tt -t> Asrt} {P' : tt' -t> Asrt} {ε : LExit}
    {Φ : Val → tt -t> Asrt} {Φ' : Val → tt' -t> Asrt}
    (f : TeleArg tt → TeleArg tt')
    (hpre : ∀ args, ⊨ (P'.apply (f args) →ₕ P.apply args))
    (hpost : ∀ v args, ⊨ (Φ v).apply args →ₕ (Φ' v).apply (f args))
    (hexpr : ∀ args, e.apply args = e'.apply (f args))
    (h : UXFrameTriple Λ ⟨P', e', ε, Φ'⟩) :
    UXFrameTriple Λ ⟨P, e, ε, Φ⟩ := by
  intro args v h' hΦ
  obtain ⟨hh, hP', ⟨εₛ, hε, hstep⟩⟩ := h (f args) v h' (hpost v args h' hΦ)
  exact ⟨hh, hpre args hh hP', εₛ, hε, by simpa only [hexpr] using hstep⟩

/-! #### Soundness of the individual atomic-command proof rules -/

/-- Soundness of the `pure` rule. -/
theorem uxframe_pure {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Pure)]) Λ ⟨fun _ => .emp, fun p => .pure p,
      .lok, fun r p => ⌞ some r = p.eval ⌟⟩ := by
  rintro p r h' ⟨rfl, hΦ⟩
  simp_all [TeleFun.apply]
  exact ⟨_, rfl, .pure hΦ.symm⟩

/-- Soundness of the `assume` rule. -/
theorem uxframe_assume {Λ : Library} :
    UXFrameTriple (tt := [tele]) Λ ⟨.emp, .assume .true,
      .lok, fun r => ⌞ r = .unit ⌟⟩ := by
  rintro args v h' ⟨rfl, rfl⟩
  exact ⟨∅, by tauto, .ok .unit, rfl, .assume⟩

/-- Soundness of the `error` rule. -/
theorem uxframe_error {Λ : Library} :
    UXFrameTriple (tt := [tele]) Λ ⟨.emp, .error,
      .lerr, fun r => ⌞ r = .unit ⌟⟩ := by
  rintro args v h' ⟨rfl, rfl⟩
  exact ⟨∅, by tauto, .err, rfl, .error⟩

/-- Soundness of the `alloc` rule. -/
theorem uxframe_alloc {Λ : Library} :
    UXFrameTriple (tt := [tele]) Λ ⟨.emp, .alloc (.int 1),
      .lok, fun r => .ex fun l => ⌞ r = .loc l ⌟ ∗ l ↦?⟩ := by
  intro r h' h''
  simp [TeleFun.apply]
  rintro x rfl rfl
  exact ⟨_, rfl, .alloc rfl id rfl rfl⟩

/-- Soundness of the `free` rule. -/
theorem uxframe_free {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Loc) (_ : Val)]) Λ
    ⟨fun l v => l ↦ v, fun l _ => .free (.loc l),
    .lok, fun r l _ => ⌞ r = .unit ⌟ ∗ l ↦∅⟩ := by
  intro ⟨l, v', ⟨⟩⟩ v h' hΦ
  simp_all [TeleFun.apply]
  refine' ⟨_, rfl, .free rfl ?mapsTo hΦ.2.2 ?iDom ?hFreed⟩
  case mapsTo =>
    simp [Heap.MapsTo, PFun.singleton]
    exact ⟨rfl, rfl⟩
  case iDom =>
    simp
  case hFreed =>
    simp only [PFun.singleton, Heap.free, Heap.update, PFun.insert_insert_self]

/-- Soundness of the `freeUninit` rule. -/
theorem uxframe_freeUninit {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Loc)]) Λ
      ⟨fun l => l ↦?, fun l => .free (.loc l),
      .lok, fun r l => ⌞ r = .unit ⌟ ∗ l ↦∅⟩ := by
  intro ⟨l, ⟨⟩⟩ r h' hΦ
  simp_all [TeleFun.apply]
  refine' ⟨_, rfl, .free rfl ?mapsTo hΦ.2.2 ?iDom ?hFreed⟩
  case mapsTo =>
    simp [Heap.MapsTo, PFun.singleton]
    exact ⟨rfl, rfl⟩
  case iDom =>
    simp
  case hFreed =>
    simp only [PFun.singleton, Heap.free, Heap.update, PFun.insert_insert_self]

/-- Soundness of the `freeFreed` rule. -/
theorem uxframe_freeFreed {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Loc)]) Λ
      ⟨fun l => l ↦∅, fun l => .free (.loc l), .lerr,
      fun r l => ⌞ r = .unit ⌟ ∗ l ↦∅⟩ := by
  intro ⟨l, ⟨⟩⟩ r h' hΦ
  simp_all [TeleFun.apply]
  exact ⟨_, rfl, .freeErr rfl (by simp [Heap.MapsTo, PFun.singleton])⟩

/-- Soundness of the `store` rule. -/
theorem uxframe_store {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Loc) (_ : Val) (_ : Val)]) Λ
      ⟨fun l _ v' => l ↦ v', fun l v _ => .store (.loc l) (.val v),
      .lok, fun r l v _ => ⌞ r = .unit ⌟ ∗ l ↦ v⟩ := by
  intro ⟨l, v, v', ⟨⟩⟩ r h' hΦ
  simp_all [TeleFun.apply]
  refine' ⟨_, rfl, .store rfl rfl ?mapsTo ?iDom ?vStored⟩
  case mapsTo =>
    simp [Heap.MapsTo, PFun.singleton]
    exact ⟨rfl, rfl⟩
  case iDom =>
    simp [hΦ.2.2]
  case vStored =>
    simp only [hΦ.2.2, Heap.store, Heap.update, BlockHeap.update,
      PFun.singleton, PFun.insert_insert_self]

/-- Soundness of the `storeUninit` rule. -/
theorem uxframe_storeUninit {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Loc) (_ : Val)]) Λ
      ⟨fun l _ => l ↦?, fun l v => .store (.loc l) (.val v),
      .lok, fun r l v => ⌞ r = .unit ⌟ ∗ l ↦ v⟩ := by
  intro ⟨l, v, ⟨⟩⟩ r h' hΦ
  simp_all [TeleFun.apply]
  refine' ⟨_, rfl, .store rfl rfl ?mapsTo ?iDom ?vStored⟩
  case mapsTo =>
    simp [Heap.MapsTo, PFun.singleton]
    exact ⟨rfl, rfl⟩
  case iDom =>
    simp [hΦ.2.2]
  case vStored =>
    simp only [hΦ.2.2, Heap.store, Heap.update, BlockHeap.update,
      PFun.singleton, PFun.insert_insert_self]

/-- Soundness of the `storeFreed` rule. -/
theorem uxframe_storeFreed {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Loc) (_ : Val)]) Λ
      ⟨fun l _ => l ↦∅, fun l v => .store (.loc l) (.val v),
      .lerr, fun r l _ => ⌞ r = .unit ⌟ ∗ l ↦∅⟩ := by
  intro ⟨l, v, _⟩ r h' hΦ
  simp_all [TeleFun.apply]
  exact ⟨_, rfl, .storeErr rfl (by simp [Heap.MapsTo, PFun.singleton])⟩

/-- Soundness of the `load` rule. -/
theorem uxframe_load {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Loc) (_ : Val)]) Λ
      ⟨fun l v => l ↦ v, fun l _ => .load (.loc l), .lok,
      fun r l v => ⌞ r = v ⌟ ∗ l ↦ v⟩ := by
  intro ⟨l, v', ⟨⟩⟩ v h' hΦ
  simp_all [TeleFun.apply]
  refine' ⟨_, rfl, .load rfl ?mapsTo ?vLoaded⟩
  case mapsTo =>
    simp [Heap.MapsTo, PFun.singleton]
    exact ⟨rfl, rfl⟩
  case vLoaded =>
    simp [BlockHeap.MapsTo, hΦ.2.2]

/-- Soundness of the `loadUninit` rule. -/
theorem uxframe_loadUninit {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Loc)]) Λ
      ⟨fun l => l ↦?, fun l => .load (.loc l), .lerr,
      fun r l => ⌞ r = .unit ⌟ ∗ l ↦?⟩ := by
  intro ⟨l, ⟨⟩⟩ v h' hΦ
  simp_all [TeleFun.apply]
  refine' ⟨_, rfl, .loadErrBlock rfl ?mapsTo ?vLoaded⟩
  case mapsTo =>
    simp [Heap.MapsTo, PFun.singleton]
    exact ⟨rfl, rfl⟩
  case vLoaded =>
    simp [BlockHeap.MapsTo, hΦ.2.2]

/-- Soundness of the `loadFreed` rule. -/
theorem uxframe_loadFreed {Λ : Library} :
    UXFrameTriple (tt := [tele (_ : Loc)]) Λ
      ⟨fun l => l ↦∅, fun l => .load (.loc l), .lerr,
      fun r l => ⌞ r = .unit ⌟ ∗ l ↦∅⟩ := by
  intro ⟨l, ⟨⟩⟩ v h' hΦ
  simp_all [TeleFun.apply]
  exact ⟨_, rfl, .loadErr rfl (by simp [Heap.MapsTo, PFun.singleton])⟩

/-- Soundness of the RISL proof rules relative to a sound, `lmiss`-free
specification context. -/
theorem WfSpec.sound {Λ : Library} {tt : Tele} {Γ : SpecCtx} {triple : SymTriple tt}
    (h : WfSpec Γ triple) :
    SpecCtxNoMiss Γ → SoundSpecCtx Λ Γ → UXFrameTriple Λ triple := by
  induction h with
  | pure => exact fun _ _ => uxframe_pure
  | assume => exact fun _ _ => uxframe_assume
  | error => exact fun _ _ => uxframe_error
  | letIn h₁ h₂ ih₁ ih₂ => exact fun hnm hΓ => uxframe_letIn (ih₁ hnm hΓ) (ih₂ hnm hΓ)
  | letCut h hne ih => exact fun hnm hΓ => uxframe_letCut (ih hnm hΓ) hne
  | choice he h ih => exact fun hnm hΓ => uxframe_choice he (ih hnm hΓ)
  | alloc => exact fun _ _ => uxframe_alloc
  | free => exact fun _ _ => uxframe_free
  | freeUninit => exact fun _ _ => uxframe_freeUninit
  | freeFreed => exact fun _ _ => uxframe_freeFreed
  | store => exact fun _ _ => uxframe_store
  | storeUninit => exact fun _ _ => uxframe_storeUninit
  | storeFreed => exact fun _ _ => uxframe_storeFreed
  | load => exact fun _ _ => uxframe_load
  | loadUninit => exact fun _ _ => uxframe_loadUninit
  | loadFreed => exact fun _ _ => uxframe_loadFreed
  | frame h ih => exact fun hnm hΓ => uxframe_frame (h.exit_ne_lmiss hnm) (ih hnm hΓ)
  | disj h₁ h₂ ih₁ ih₂ => exact fun hnm hΓ => uxframe_disj (ih₁ hnm hΓ) (ih₂ hnm hΓ)
  | cons f hsub hpre hpost hexpr h ih =>
      exact fun hnm hΓ =>
        uxframe_cons f hpre hpost hexpr (ih (hnm.mono hsub) (hΓ.mono hsub))
  | ex h ih => exact fun hnm hΓ => uxframe_ex (ih hnm hΓ)
  | call hmem => exact fun _ hΓ => hΓ _ _ hmem

/-- Soundness of well-formed specification contexts: they are both `lmiss`-free and semantically sound. -/
theorem WfSpecCtx.sound {Λ : Library} {Γ : SpecCtx} (h : Λ ≺ₛ Γ) :
    SpecCtxNoMiss Γ ∧ SoundSpecCtx Λ Γ := by
  induction h
  · simp [SpecCtxNoMiss, SoundSpecCtx]
  · rename_i f _ _ _ _ _ _ _ _ _ _ hmaps hspec hctx
    obtain ⟨hmiss, hctx⟩ := hctx
    simp_all [SpecCtxNoMiss, SoundSpecCtx]
    refine ⟨?_, ?_⟩ <;> intro f' s hin <;>
      by_cases hf : f' = f <;> simp_all [SpecCtx.update]
    · subst hf
      rw [Function.update_self] at hin
      rcases List.mem_cons.1 hin with rfl | hin
      · exact hspec.exit_ne_lmiss hmiss
      · exact hmiss _ _ hin
    · exact hmiss _ _ hin
    · subst hf
      rw [Function.update_self] at hin
      rcases List.mem_cons.1 hin with rfl | hin
      · exact callTriple_of_body hmaps (hspec.sound hmiss hctx)
      · exact hctx _ _ hin

/-- RISL instantiated as a sound UX logic for the refutation algorithm
(`risl`). -/
def risl : Logic where
  DerivableSpec Λ triple := ∃ Γ, Λ ≺ₛ Γ ∧ WfSpec Γ triple
  ux_frame_soundness := by
    intro tt Λ triple ⟨Γ, hctx, hwf⟩
    obtain ⟨hnm, hsound⟩ := hctx.sound
    exact hwf.sound hnm hsound

end RUXt
