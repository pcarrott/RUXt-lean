/-
Port of `theories/model/logic.v`: template for a sound under-approximate
program logic.
-/
import RUXt.Lang.Semantics
import RUXt.Lang.Assertion
import RUXt.Model.TypeChecker

namespace RUXt

open scoped RUXt.PMap

universe u

/-! ### UX semantics -/

/-- `ux_triple`: under-approximate (incorrectness) triples for a given
evaluation relation. -/
def UXTriple (eval : ImplCtx → Heap → Expr → Heap → Exit → Prop)
    (γ : ImplCtx) (e : Expr) (P Q : Asrt) (ε : Exit) : Prop :=
  ∀ h', hprop h' Q → ∃ h, hprop h P ∧ eval γ h e h' ε

/-- `ux_frame_triple`. -/
def UXFrameTriple (γ : ImplCtx) (e : Expr) (P Q : Asrt) (ε : Exit) : Prop :=
  UXTriple FrameStep γ e P Q ε

/-- `ux_full_triple`. -/
def UXFullTriple (γ : ImplCtx) (e : Expr) (P Q : Asrt) (ε : Exit) : Prop :=
  UXTriple BigStep γ e P Q ε

/-- `ux_triple_preservation`. -/
theorem ux_triple_preservation {γ : ImplCtx} {e : Expr} {P Q : Asrt} {ε : Exit}
    (hux : UXFrameTriple γ e P Q ε) : UXFullTriple γ e P Q ε.toFull := by
  intro h' hQ
  obtain ⟨h, hP, hstep⟩ := hux h' hQ
  exact ⟨h, hP, semantics_preservation hstep⟩

/-! ### Sound UX logics -/

/-- `logic`: the refutation algorithm requires a logic that derives UX
specifications. -/
structure Logic : Type 1 where
  DerivableSpec : ImplCtx → Expr → Asrt → Asrt → Exit → Prop
  ux_frame_soundness {γ : ImplCtx} {e : Expr} {P Q : Asrt} {ε : Exit} :
    DerivableSpec γ e P Q ε → UXFrameTriple γ e P Q ε

/-- `ux_soundness`. -/
theorem Logic.ux_soundness (L : Logic) {γ : ImplCtx} {e : Expr} {P Q : Asrt} {ε : Exit}
    (hspec : L.DerivableSpec γ e P Q ε) : UXFullTriple γ e P Q ε.toFull :=
  ux_triple_preservation (L.ux_frame_soundness hspec)

/-! ### Values and satisfiable postconditions -/

/-- `sat_post`. -/
def satPost (Q : Val → Asrt) : Prop := ∃ v, sat (Q v)

/-- `val_post`. -/
def valPost (kind : BaseType) (v : Val) : Asrt :=
  match kind with
  | .int => ⌞∃ z, v = .int z⌟
  | .bool => ⌞∃ b, v = .bool b⌟
  | .loc => ⌞∃ l, v = .loc l⌟
  | .unit => ⌞v = .unit⌟

/-- `val_post_sat`. -/
theorem valPost_sat (kind : BaseType) : satPost (valPost kind) := by
  cases kind
  · exact ⟨.int 0, ∅, rfl, 0, rfl⟩
  · exact ⟨.bool Bool.true, ∅, rfl, Bool.true, rfl⟩
  · exact ⟨.loc (1, 0), ∅, rfl, (1, 0), rfl⟩
  · exact ⟨.unit, ∅, rfl, rfl⟩

/-! ### UX properties -/

/-- `pure_val_spec`. -/
theorem pure_val_spec (γ : ImplCtx) (v : Val) :
    UXFrameTriple γ (.pure (.val v)) .emp (valPost v.baseType v) (.ok v) := by
  intro h' hval
  refine ⟨∅, rfl, ?_⟩
  obtain rfl : h' = ∅ := by cases v <;> exact hval.1
  exact .pure rfl

/-- `let_spec`. -/
theorem let_spec {γ : ImplCtx} {x : Binder} {e₁ e₂ : Expr} {P Q R : Asrt} {v : Val} {ε : Exit}
    (hux₁ : UXFrameTriple γ e₁ P R (.ok v))
    (hux₂ : UXFrameTriple γ (e₂.subst x v) R Q ε) :
    UXFrameTriple γ (.letIn x e₁ e₂) P Q ε := by
  intro h' hQ
  obtain ⟨h'', hR, hstep₂⟩ := hux₂ h' hQ
  obtain ⟨h, hP, hstep₁⟩ := hux₁ h'' hR
  exact ⟨h, hP, .letIn hstep₁ hstep₂⟩

/-- `frame_app_spec`. -/
theorem frame_app_spec {X : Type u} {γ : ImplCtx} {e : Expr} (xs : List X) {x : X}
    {P : X → Asrt} {v : Val}
    (hux : UXFrameTriple γ e .emp (P x) (.ok v)) :
    UXFrameTriple γ e (Asrt.iter xs P) (Asrt.iter (xs ++ [x]) P) (.ok v) := by
  intro h' happ
  rw [hiter_app] at happ
  obtain ⟨hxs, hx, rfl, hdisj, hPxs, hPx⟩ := happ
  rw [hiter_singleton] at hPx
  obtain ⟨h₀, (rfl : h₀ = ∅), hstep⟩ := hux hx hPx
  rcases frame_addition hstep hxs hdisj.symm with ⟨hstepF, -⟩ | ⟨l, hl, -⟩
  · refine ⟨hxs, hPxs, ?_⟩
    rw [PMap.empty_union] at hstepF
    rwa [PMap.union_comm hdisj]
  · exact absurd hl (by simp)

/-- `call_spec`. -/
theorem call_spec {γ : ImplCtx} {f : String} {xs : List String} {e : Expr}
    {vs : List Val} {P Q : Asrt} {ε : Exit}
    (hsome : γ f = some ⟨xs, e⟩) :
    UXFrameTriple γ (.call f (Term.ofVals vs)) P Q ε ↔
    UXFrameTriple γ (e.substs xs (Term.ofVals vs)) P Q ε := by
  constructor
  · intro hux h' hQ
    obtain ⟨h, hP, hcall⟩ := hux h' hQ
    cases hcall with
    | call hf hstep =>
      rw [hsome] at hf
      simp only [Option.some.injEq, FunImpl.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨h, hP, hstep⟩
  · intro hux h' hQ
    obtain ⟨h, hP, hstep⟩ := hux h' hQ
    exact ⟨h, hP, .call hsome hstep⟩

end RUXt
