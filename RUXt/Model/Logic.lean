import RUXt.Lib.Telescopes
import RUXt.Model.Assertion

namespace RUXt

/-! ### Symbolic triples -/

/-- Termination tags at the logic level. -/
inductive LExit
  | lok : LExit
  | lerr : LExit
  | lmiss : LExit
/-- Symbolic triples. -/
def SymTriple (tt : Tele) : Type 1 :=
  (tt -t> Asrt) × (tt -t> Expr) × LExit × (Val → tt -t> Asrt)
/-- The exit tag of a function specification. -/
def SymTriple.exit {tt : Tele} : SymTriple tt → LExit
  | ⟨_, _, ε, _⟩ => ε

/-- Converts a logical tag to a semantic one, given a value.
If the value does not match the expected tag, returns `none`. -/
def LExit.toExit : LExit → Val → Option Exit
  | .lok, v => some (.ok v)
  | .lerr, .unit => some .err
  | .lmiss, .loc l => some (.miss l)
  | _, _ => none

/-! ### UX semantics -/

/-- Under-approximate semantic triples for a given big-step relation. -/
def UXTriple {tt : Tele} (step : Library → Heap → Expr → Heap → Exit → Prop)
    : Library → SymTriple tt → Prop
  | Λ, ⟨P, e, εₗ, Φ⟩  =>
    ∀ args v h', HProp h' ((Φ v).apply args) → ∃ h, HProp h (P.apply args) ∧
    ∃ εₛ, εₗ.toExit v = some εₛ ∧ step Λ h (e.apply args) h' εₛ
/-- Under-approximate semantic triples for the instrumented semantics. -/
def UXFrameTriple {tt : Tele} : Library → SymTriple tt → Prop := UXTriple FrameStep
/-- Under-approximate semantic triples for the full semantics. -/
def UXFullTriple {tt : Tele} : Library → SymTriple tt → Prop := UXTriple BigStep

/-- Maps a triple with a `miss` exit to one with an `err` exit. -/
def mapMissToErr {tt : Tele} : SymTriple tt → SymTriple tt
  | ⟨P, e, .lmiss, Φ⟩ => ⟨P, e, .lerr, fun v => teleBind (fun args =>
      ⌞ v = .unit ⌟ ∗ Asrt.ex fun l => (Φ (.loc l)).apply args)⟩
  | triple => triple
/-- Preserved behaviour between the instrumented and the full triples. -/
theorem ux_triple_preservation {tt : Tele} {Λ : Library} {triple : SymTriple tt}
    (hux : UXFrameTriple Λ triple) : UXFullTriple Λ (mapMissToErr triple) := by
  intro args v h' hΦ
  obtain ⟨P, e, εₗ, Φ⟩ := triple
  cases εₗ <;> simp [*] at *
  · obtain ⟨h, hP, ε, Hε, hstep⟩ := hux _ _ _ hΦ
    obtain hstep := semantics_preservation hstep
    cases Hε
    exact ⟨h, hP, .ok v, rfl, hstep⟩
  · obtain ⟨h, hP, ε, Hε, hstep⟩ := hux _ _ _ hΦ
    obtain hstep := semantics_preservation hstep
    let .unit := v
    cases Hε
    exact ⟨h, hP, .err, rfl, hstep⟩
  · rw [teleBind_apply] at hΦ
    obtain ⟨h1', h', rfl, hdisj, ⟨rfl, rfl⟩, hΦ⟩ := hΦ
    rw [<- PFun.union_id_l]
    obtain ⟨l, hΦ⟩ := hΦ
    obtain ⟨h, hP, ε, Hε, hstep⟩ := hux _ _ _ hΦ
    obtain hstep := semantics_preservation hstep
    cases Hε
    exact ⟨h, hP, .err, rfl, hstep⟩

theorem ux_frame_triple_spec {tt : Tele} {Λ : Library}
    {P : tt -t> Asrt} {e : tt -t> Expr} {εₗ : LExit} {Φ : Val → tt -t> Asrt}
    (hux : UXFrameTriple Λ ⟨P, e, εₗ, Φ⟩) :
    ∀ args r h', HProp h' ((Φ r).apply args) → ∀ ε, εₗ.toExit r = some ε →
    ∃ h, HProp h (P.apply args) ∧ Λ ⊢ ⟨ h | e.apply args ⟩ ⇓ ⟨ h' | ε.toFull ⟩ := by
  intro args r h' hΦ ε hε
  obtain hux := ux_triple_preservation hux
  cases εₗ
  · cases hε
    obtain ⟨h, hP, ε, Hε, hstep⟩ := hux _ _ _ hΦ
    cases Hε
    exact ⟨h, hP, hstep⟩
  · let .unit := r
    cases hε
    obtain ⟨h, hP, ε, hε, hstep⟩ := hux _ _ _ hΦ
    cases hε
    exact ⟨h, hP, hstep⟩
  · let .loc ⟨b, i⟩ := r
    cases hε
    specialize hux args .unit h' ?_
    · simp_all [teleBind_apply]
      exact ⟨b, i, hΦ⟩
    obtain ⟨h, hP, ε, hε, hstep⟩ := hux
    cases hε
    exact ⟨h, hP, hstep⟩

/-! ### UX logics -/

/-- The refutation algorithm requires a logic that derives sound UX specifications. -/
structure Logic : Type 1 where
  DerivableSpec {tt : Tele} : Library → SymTriple tt → Prop
  ux_frame_soundness {tt : Tele} {Λ : Library} {triple : SymTriple tt} :
    DerivableSpec Λ triple → UXFrameTriple Λ triple

end RUXt
