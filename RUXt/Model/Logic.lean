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
    ∀ args v h', hprop h' ((Φ v).apply args) → ∃ h, hprop h (P.apply args) ∧
    ∃ εₛ, εₗ.toExit v = some εₛ ∧ step Λ h (e.apply args) h' εₛ
/-- Under-approximate semantic triples for the instrumented semantics. -/
def UXFrameTriple {tt : Tele} : Library → SymTriple tt → Prop := UXTriple FrameStep
/-- Under-approximate semantic triples for the full semantics. -/
def UXFullTriple {tt : Tele} : Library → SymTriple tt → Prop := UXTriple BigStep

/-- Maps a triple with a `miss` exit to one with an `err` exit. -/
def MapMissToErr {tt : Tele} : SymTriple tt → SymTriple tt
  | ⟨P, e, .lmiss, Φ⟩ => ⟨P, e, .lerr, fun v => teleBind (fun args =>
      ⌞ v = .unit ⌟ ∗ Asrt.ex fun l => (Φ (.loc l)).apply args)⟩
  | triple => triple
/-- Preserved behaviour between the instrumented and the full triples. -/
theorem ux_triple_preservation {tt : Tele} {Λ : Library} {triple : SymTriple tt}
    (hux : UXFrameTriple Λ triple) : UXFullTriple Λ (MapMissToErr triple) := by
  intro args v h' hΦ
  obtain ⟨P, e, εₗ, Φ⟩ := triple
  cases εₗ <;> simp [*] at *
  · obtain ⟨h, hP, ε, Hε, hstep⟩ := hux _ _ _ hΦ
    obtain hstep := semantics_preservation hstep
    injection Hε with Hε; subst Hε
    exact ⟨h, hP, .ok v, rfl, hstep⟩
  · obtain ⟨h, hP, ε, Hε, hstep⟩ := hux _ _ _ hΦ
    obtain hstep := semantics_preservation hstep
    let .unit := v
    injection Hε with Hε; subst Hε
    exact ⟨h, hP, .err, rfl, hstep⟩
  · rw [teleBind_apply] at hΦ
    obtain ⟨h1', h', rfl, hdisj, ⟨rfl, rfl⟩, hΦ⟩ := hΦ
    rw [<- PMap.union_id_l]
    obtain ⟨l, hΦ⟩ := hΦ
    obtain ⟨h, hP, ε, Hε, hstep⟩ := hux _ _ _ hΦ
    obtain hstep := semantics_preservation hstep
    injection Hε with Hε; subst Hε
    exact ⟨h, hP, .err, rfl, hstep⟩

theorem ux_frame_triple_spec {tt : Tele} {Λ : Library}
    {P : tt -t> Asrt} {e : tt -t> Expr} {εₗ : LExit} {Φ : Val → tt -t> Asrt}
    (hux : UXFrameTriple Λ ⟨P, e, εₗ, Φ⟩) :
    ∀ args r h', hprop h' ((Φ r).apply args) → ∀ ε, εₗ.toExit r = some ε →
    ∃ h, hprop h (P.apply args) ∧ Λ ⊢ ⟨ h | e.apply args ⟩ ⇓ ⟨ h' | ε.toFull ⟩ := by
  intro args r h' hΦ ε hε
  obtain hux := ux_triple_preservation hux
  cases εₗ
  · injection hε with hε; subst hε
    obtain ⟨h, hP, ε, Hε, hstep⟩ := hux _ _ _ hΦ
    injection Hε with Hε; subst Hε
    exact ⟨h, hP, hstep⟩
  · let .unit := r
    injection hε with hε; subst hε
    obtain ⟨h, hP, ε, hε, hstep⟩ := hux _ _ _ hΦ
    injection hε with hε; subst hε
    exact ⟨h, hP, hstep⟩
  · let .loc ⟨b, i⟩ := r
    injection hε with hε; subst hε
    specialize hux args .unit h' ?_
    · rw [teleBind_apply]
      simp [*] at *
      exact ⟨b, i, hΦ⟩
    · obtain ⟨h, hP, ε, hε, hstep⟩ := hux
      injection hε with hε; subst hε
      exact ⟨h, hP, hstep⟩

/-! ### UX logics -/

/-- The refutation algorithm requires a logic that derives sound UX specifications. -/
structure Logic : Type 1 where
  DerivableSpec {tt : Tele} : Library → SymTriple tt → Prop
  ux_frame_soundness {tt : Tele} {Λ : Library} {triple : SymTriple tt} :
    DerivableSpec Λ triple → UXFrameTriple Λ triple

/-! ### Values and satisfiable postconditions -/

-- /-- `sat_post`. -/
-- def satPost (Q : Val → Asrt) : Prop := ∃ v, sat (Q v)

-- /-- `val_post`. -/
-- def valPost (kind : BaseType) (v : Val) : Asrt :=
--   match kind with
--   | .int => ⌞∃ z, v = .int z⌟
--   | .bool => ⌞∃ b, v = .bool b⌟
--   | .loc => ⌞∃ l, v = .loc l⌟
--   | .unit => ⌞v = .unit⌟

-- /-- `val_post_sat`. -/
-- theorem valPost_sat (kind : BaseType) : satPost (valPost kind) := by
--   cases kind
--   · exact ⟨.int 0, ∅, rfl, 0, rfl⟩
--   · exact ⟨.bool Bool.true, ∅, rfl, Bool.true, rfl⟩
--   · exact ⟨.loc (1, 0), ∅, rfl, (1, 0), rfl⟩
--   · exact ⟨.unit, ∅, rfl, rfl⟩

/-! ### UX properties -/

-- /-- `pure_val_spec`. -/
-- theorem pure_val_spec (Λ : Library) (v : Val) :
--     UXFrameTriple Λ (.pure (.val v)) .emp (valPost v.baseType v) (.ok v) := by
--   intro h' hval
--   refine ⟨∅, rfl, ?_⟩
--   obtain rfl : h' = ∅ := by cases v <;> exact hval.1
--   exact .pure rfl

-- /-- `let_spec`. -/
-- theorem let_spec {Λ : Library} {x : Binder} {e₁ e₂ : Expr} {P Q R : Asrt} {v : Val} {ε : Exit}
--     (hux₁ : UXFrameTriple Λ e₁ P R (.ok v))
--     (hux₂ : UXFrameTriple Λ (e₂.subst x v) R Q ε) :
--     UXFrameTriple Λ (.letIn x e₁ e₂) P Q ε := by
--   intro h' hQ
--   obtain ⟨h'', hR, hstep₂⟩ := hux₂ h' hQ
--   obtain ⟨h, hP, hstep₁⟩ := hux₁ h'' hR
--   exact ⟨h, hP, .letIn hstep₁ hstep₂⟩

-- /-- `frame_app_spec`. -/
-- theorem frame_app_spec {X : Type u} {Λ : Library} {e : Expr} (xs : List X) {x : X}
--     {P : X → Asrt} {v : Val}
--     (hux : UXFrameTriple Λ e .emp (P x) (.ok v)) :
--     UXFrameTriple Λ e (Asrt.iter xs P) (Asrt.iter (xs ++ [x]) P) (.ok v) := by
--   intro h' happ
--   rw [hiter_app] at happ
--   obtain ⟨hxs, hx, rfl, hdisj, hPxs, hPx⟩ := happ
--   rw [hiter_singleton] at hPx
--   obtain ⟨h₀, (rfl : h₀ = ∅), hstep⟩ := hux hx hPx
--   rcases frame_addition hstep hxs hdisj.symm with ⟨hstepF, -⟩ | ⟨l, hl, -⟩
--   · refine ⟨hxs, hPxs, ?_⟩
--     rw [PMap.empty_union] at hstepF
--     rwa [PMap.union_comm hdisj]
--   · exact absurd hl (by simp)

-- /-- `call_spec`. -/
-- theorem call_spec {Λ : Library} {f : String} {xs : List String} {e : Expr}
--     {vs : List Val} {P Q : Asrt} {ε : Exit}
--     (hsome : Λ.get f = some ⟨xs, e⟩) :
--     UXFrameTriple Λ (.call f (Term.ofVals vs)) P Q ε ↔
--     UXFrameTriple Λ (e.substs xs (Term.ofVals vs)) P Q ε := by
--   constructor
--   · intro hux h' hQ
--     obtain ⟨h, hP, hcall⟩ := hux h' hQ
--     cases hcall with
--     | call hf hstep =>
--       rw [hsome] at hf
--       simp only [Option.some.injEq, FunImpl.mk.injEq] at hf
--       obtain ⟨rfl, rfl⟩ := hf
--       exact ⟨h, hP, hstep⟩
--   · intro hux h' hQ
--     obtain ⟨h, hP, hstep⟩ := hux h' hQ
--     exact ⟨h, hP, .call hsome hstep⟩

end RUXt
