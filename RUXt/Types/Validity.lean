/-
Port of `theories/types/validity.v`: properties relating OX and UX reasoning.
-/
import RUXt.Lib.PMap
import RUXt.Lang.Semantics
import RUXt.Types.Rules
import RUXt.Model.Logic
import RUXt.Model.Refute

namespace RUXt

open scoped RUXt.PMap

/-! ### Reasoning principles for triples -/

/-- `principle_of_agreement`. -/
theorem principle_of_agreement {eval : ImplCtx → Heap → Expr → Heap → Exit → Prop}
    {γ : ImplCtx} {e : Expr} {Pox : Asrt} {Qoxf : Val → Asrt} {Pux Qux : Asrt} {ε : Exit}
    (hux : UXTriple eval γ e Pux Qux ε)
    (hPimp : ⊨ (Pux →ₕ Pox))
    (hox : OXTriple eval γ e Pox Qoxf) :
    ⊨ (Qux →ₕ .ex fun v => ⌞ε = .ok v⌟ ∗ Qoxf v) := by
  intro h hQux;
  obtain ⟨ h₀, hPux, hε ⟩ := hux h hQux;
  obtain ⟨ v, hv₁, hv₂ ⟩ := hox h₀ ( hPimp h₀ hPux ) h ε hε;
  simp +decide [ hv₁, hv₂, hprop_pure ]

/-- `principle_of_denial`. -/
theorem principle_of_denial {eval : ImplCtx → Heap → Expr → Heap → Exit → Prop}
    {γ : ImplCtx} {e : Expr} {Pox : Asrt} {Qoxf : Val → Asrt} {Pux Qux : Asrt} {ε : Exit}
    (hux : UXTriple eval γ e Pux Qux ε)
    (hPimp : ⊨ (Pux →ₕ Pox))
    (hnQimp : ¬ (⊨ (Qux →ₕ .ex fun v => ⌞ε = .ok v⌟ ∗ Qoxf v))) :
    ¬ OXTriple eval γ e Pox Qoxf := by
  exact fun h => hnQimp <| principle_of_agreement hux hPimp h

/-! ### Interpretation contexts

An interpretation context maps type identifiers to their semantic
interpretation. In the Rocq development it is a `gmap tid type` accessed only
through the total lookup `!!!` with the `Inhabited` default `unit`; total
functions are the faithful counterpart. -/

/-- `interp_ctx`. -/
def InterpCtx := Tid → Ty

/-- `type_inhabited`. -/
instance : Inhabited Ty := ⟨unit⟩

/-- `to_type`. -/
def toType (𝕀 : InterpCtx) (τ : Tid) : Ty := 𝕀 τ

/-- `to_types`. -/
def toTypes (𝕀 : InterpCtx) (τs : List Tid) : List Ty := τs.map (toType 𝕀)

/-- `to_type_ctx` (pointwise counterpart of the `map_fold` over
`insert_fun_type`). -/
def toTypeCtx (Δ : SignCtx) (𝕀 : InterpCtx) : TypeCtx :=
  fun f => (Δ f).map fun s => ⟨toTypes 𝕀 s.tyIn, toType 𝕀 s.tyOut⟩

/-- `lookup_type_sign_Some`. -/
theorem lookup_type_sign_some {Δ : SignCtx} {𝕀 : InterpCtx} {f : String}
    {τs : List Tid} {τ : Tid} (htype : Δ f = some ⟨τs, τ⟩) :
    toTypeCtx Δ 𝕀 f = some ⟨toTypes 𝕀 τs, toType 𝕀 τ⟩ := by
  unfold toTypeCtx; aesop;

/-! ### Type soundness and refutation -/

/-- `is_subvariant`: a safe context constitutes a valid type subvariant. -/
def IsSubvariant (𝕀 : InterpCtx) (τs : List Tid) (vs : List Val) (P : Asrt)
    (_ : List Expr) : Prop :=
  ⊨ (P →ₕ [∗ₜ vs [⊲] boxes (toTypes 𝕀 τs)])

/-- `type_sound`: a library `Λ` is type-sound wrt the semantic interpretation
of `𝕀`. -/
def TypeSound (Λ : Library) (𝕀 : InterpCtx) : Prop :=
  ValidTypeCtx Λ.impls (toTypeCtx Λ.types 𝕀)

/-- Derivable states must satisfy the output type invariant
(`principle_of_validity`). -/
theorem principle_of_validity {Λ : Library} {𝕀 : InterpCtx} {e : Expr} {τ : Tid}
    {Q : Asrt} {ε : Exit}
    (hsound : TypeSound Λ 𝕀) (hpost : DerivablePost (IsSubvariant 𝕀) Λ τ ε Q e) :
    ⊨ (Q →ₕ .ex fun v => ⌞ε = .ok v⌟ ∗ [∗ₜ [v ⊲ box (toType 𝕀 τ)]]) := by
  contrapose! hpost;
  rintro ⟨ hsub, hspec ⟩;
  obtain ⟨ τs, htype, vs, P, es, hsub, L, hspec, xs, rfl, hxs₁, hxs₂ ⟩ := hspec;
  have := principle_of_agreement ( L.ux_frame_soundness hspec ) hsub ( RUXt.ox_call hsound ( lookup_type_sign_some htype ) ) ; tauto;

/-- `ub_derivable`: undefined behaviour is provably reachable. -/
def UBDerivable (Λ : Library) (𝕀 : InterpCtx) : Prop :=
  ∃ e τ Q ε, DerivablePost (IsSubvariant 𝕀) Λ τ ε Q e ∧ sat Q ∧ ¬ ∃ v, ε = .ok v

/-- Type-sound libraries must never exhibit undefined behaviour
(`type_unsoundness`). -/
theorem type_unsoundness {Λ : Library} {𝕀 : InterpCtx} (hub : UBDerivable Λ 𝕀) :
    ¬ TypeSound Λ 𝕀 := by
  intro hTypeSound;
  obtain ⟨ e, τ, Q, ε, hpost, ⟨ hwit, hsatQ ⟩, hnv ⟩ := hub;
  have := principle_of_validity hTypeSound hpost;
  specialize this hwit hsatQ;
  cases this ; simp_all +decide [ hprop ]

end RUXt