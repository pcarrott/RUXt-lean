import RUXt.Lang.Library

namespace RUXt

/-! ### Base types -/

def Val.baseTy : Val → BaseType
  | .int _ => .int
  | .bool _ => .bool
  | .loc _ => .loc
  | .unit => .unit

def Val.ty : Val → Ty
  | v => .base v.baseTy


/-! ### Typed variable contexts -/

/-- Typed variable contexts. -/
abbrev VarCtx := PFun PVar Ty

def consVarCtx (xs : List PVar) (τs : List Ty) : VarCtx :=
  (xs.zip τs).foldr (fun (x, τ) 𝕍 => 𝕍.insert x τ) ∅

def VarCtx.consFrom (𝕍 : VarCtx) (xs : List PVar) (τs : List Ty) : VarCtx :=
  (xs.zip τs).foldl (fun 𝕍 (x, τ) => 𝕍.insert x τ) 𝕍

private theorem consVarCtx_insert {xs : List PVar} {τs : List Ty} (x : PVar) (τ : Ty) :
    (consVarCtx xs τs).insert x τ = consVarCtx (x :: xs) (τ :: τs) := rfl

private theorem consVarCtx_lookup_none {xs : List PVar} {τs : List Ty} {x : PVar}
    (hnin : x ∉ xs) : consVarCtx xs τs x = Part.none := by
  induction xs generalizing τs with
  | nil => rfl
  | cons y ys ih =>
    cases τs with
    | nil => simp [consVarCtx]
    | cons τ τs =>
      simp only [List.mem_cons, not_or] at hnin
      rw [← consVarCtx_insert y τ, PFun.insert_apply_ne _ _ hnin.1]
      exact ih hnin.2

theorem consVarCtx_eq_rev {xs : List PVar} {τs : List Ty} (hdup : xs.Nodup) :
    (∅ : VarCtx).consFrom xs τs = consVarCtx xs τs := by
  have h_consVarCtx {xs : List PVar} {τs : List Ty} : xs.Nodup →
      ∀ (𝕍 : VarCtx),
        List.foldl (fun 𝕍 (x, τ) => PFun.insert x τ 𝕍) 𝕍 (xs.zip τs) = (consVarCtx xs τs) ∪ 𝕍 := by
    revert τs
    induction xs with
    | nil => intro τs _ m; simp [consVarCtx, PFun.empty_union]
    | cons x xs ih =>
      intro τs hdup m
      rcases τs with _ | ⟨τ, τs⟩
      · simp [consVarCtx]
      · obtain ⟨hnin, hdup'⟩ := List.nodup_cons.mp hdup
        rw [List.zip_cons_cons, List.foldl_cons, ← consVarCtx_insert x τ,
          PFun.insert_union_l, ih hdup' (PFun.insert x τ m)]
        ext y
        by_cases hy : y = x
        · subst hy
          simp [PFun.union_apply, PFun.insert_apply,
            consVarCtx_lookup_none hnin, Part.not_none_dom]
        · simp [PFun.union_apply, PFun.insert_apply, hy]
  rw [VarCtx.consFrom, h_consVarCtx hdup ∅, PFun.union_empty]

/-! ### Well-typed terms -/

/-- A term checks against `τ` when it is a value of the right base
type or a variable bound to `τ` in the context. -/
private def CheckTerm (𝕍 : VarCtx) (t : Term) (τ : Ty) : Prop :=
  match t with
  | .var x => 𝕍 x = τ
  | .val v => Ty.base v.baseTy = τ

/-- A list of terms checks against a list of types when they have
the same length and check pointwise. -/
private def CheckTerms (𝕍 : VarCtx) : List Term → List Ty → Prop
  | [], [] => True
  | t :: ts, τ :: τs => CheckTerm 𝕍 t τ ∧ CheckTerms 𝕍 ts τs
  | _, _ => False

private theorem checkTerms_subset {𝕍 𝕍' : VarCtx} {ts : List Term} {τs : List Ty}
    (hcheck : CheckTerms 𝕍' ts τs) (hsub : 𝕍' ⊆ 𝕍) :
    CheckTerms 𝕍 ts τs := by
  induction ts generalizing τs with
  | nil => cases τs <;> simp_all [CheckTerms]
  | cons t ts ih =>
    cases τs with
    | nil => exact hcheck.elim
    | cons τ τs =>
      obtain ⟨h1, h2⟩ := hcheck
      refine ⟨?_, ih h2⟩
      cases t with
      | val v => exact h1
      | var x => exact PFun.subset_apply hsub h1

private theorem checkTerms_consVarCtx {xs : List PVar} {τs : List Ty}
    (hlen : xs.length = τs.length) (hdup : xs.Nodup) :
    CheckTerms (consVarCtx xs τs) (Term.ofVars xs) τs := by
  induction xs generalizing τs with
  | nil => cases τs <;> simp_all [CheckTerms, Term.ofVars]
  | cons x xs ih =>
    cases τs with
    | nil => simp at hlen
    | cons τ τs =>
      obtain ⟨hnin, hdup'⟩ := List.nodup_cons.mp hdup
      have hlen' : xs.length = τs.length := by simpa using hlen
      rw [← consVarCtx_insert x τ]
      simp only [Term.ofVars_cons, CheckTerms]
      refine ⟨?_, ?_⟩
      · show (PFun.insert x τ (consVarCtx xs τs)) x = τ
        simp [PFun.insert_apply]
      · refine checkTerms_subset (ih hlen' hdup') ?_
        intro a b hab
        by_cases hax : a = x
        · subst hax
          rw [consVarCtx_lookup_none hnin] at hab
          exact absurd hab (by simp)
        · rwa [PFun.insert_apply_ne _ _ hax]

private theorem checkTerms_dom {𝕍 : VarCtx} {ts : List Term} {τs : List Ty} {x : PVar}
    (hcheck : CheckTerms 𝕍 ts τs) (hin : Term.var x ∈ ts) :
    x ∈ 𝕍.dom := by
  induction ts generalizing τs with
  | nil => simp at hin
  | cons t ts ih =>
    cases τs with
    | nil => exact hcheck.elim
    | cons τ τs =>
      obtain ⟨h1, h2⟩ := hcheck
      rcases List.mem_cons.mp hin with rfl | hin'
      · have hx : 𝕍 x = τ := h1
        exact PFun.mem_dom.mpr ⟨τ, hx⟩
      · exact ih h2 hin'

/-! ### Safe programs -/

/-- `e` is a safe program of type `τ` in context `𝕍` if it only makes
calls to library functions whose arguments and result type match. -/
def SafeProgram (𝕍 : VarCtx) (Λ : Library) (e : Expr) (τ : Ty) : Prop :=
  match e with
  | .letIn bx e₁ e₂ =>
      ∃ τ₁, SafeProgram ∅ Λ e₁ τ₁ ∧
        match bx with
        | .named x => SafeProgram (𝕍.insert x τ₁) Λ e₂ τ
        | .anon => SafeProgram 𝕍 Λ e₂ τ
  | .call f ts =>
      ∃ xs body hdup, Λ.MapsTo f ⟨xs, body, τ, hdup⟩ ∧
        CheckTerms 𝕍 ts (xs.map Prod.snd)
  | .pure (.term (.val v)) => τ = v.ty
  | _ => False

/-- A main program is a safe program with no free variables. -/
def SafeMain (Λ : Library) (e : Expr) (τ : Ty) : Prop := SafeProgram ∅ Λ e τ

theorem safeMain_pure {Λ : Library} {v : Val} :
    SafeMain Λ (Expr.pure (.val v)) (v.ty) := by
  tauto

theorem safeProgram_subset {𝕍 𝕍' : VarCtx} {Λ : Library} {e : Expr} {τ : Ty}
    (hsafe : SafeProgram 𝕍' Λ e τ) (hsub : 𝕍' ⊆ 𝕍) :
    SafeProgram 𝕍 Λ e τ := by
  induction e generalizing 𝕍 𝕍' τ with
  | letIn bx e₁ e₂ ih₁ ih₂ =>
    obtain ⟨τ₁, h1, h2⟩ := hsafe
    refine ⟨τ₁, ih₁ h1 (PFun.empty_subset _), ?_⟩
    cases bx with
    | anon => exact ih₂ h2 hsub
    | named x => exact ih₂ h2 (PFun.insert_mono _ _ hsub)
  | call f ts =>
    obtain ⟨xs, body, hdup, hΛ, hcheck⟩ := hsafe
    exact ⟨xs, body, hdup, hΛ, checkTerms_subset hcheck hsub⟩
  | pure p =>
    cases p with
    | term t => cases t <;> simp_all [SafeProgram]
    | unOp op p => exact hsafe.elim
    | binOp op p₁ p₂ => exact hsafe.elim
  | _ => exact hsafe.elim

theorem safe_call {Λ : Library} {f : Fid} {xs e τ hdup}
   (htype : Λ.MapsTo f ⟨xs, e, τ, hdup⟩) :
    SafeProgram (consVarCtx (xs.map Prod.fst) (xs.map Prod.snd))
      Λ (.call f (Term.ofVars (xs.map Prod.fst))) τ :=
  ⟨xs, e, hdup, htype, checkTerms_consVarCtx (by simp) hdup⟩

private theorem safeProgram_closed {𝕍 : VarCtx} {Λ : Library} {e : Expr} {τ : Ty}
    (hsafe : SafeProgram 𝕍 Λ e τ) : e.Closed 𝕍.dom := by
  induction e generalizing 𝕍 τ with
  | letIn bx e₁ e₂ ih₁ ih₂ =>
    obtain ⟨τ₁, h1, h2⟩ := hsafe
    refine ⟨ih₁ (safeProgram_subset h1 (PFun.empty_subset _)), ?_⟩
    cases bx with
    | anon => exact ih₂ h2
    | named x =>
      have hmem := ih₂ h2
      rw [PFun.dom_insert] at hmem
      rwa [Set.union_comm] at hmem
  | call f ts =>
    obtain ⟨xs, body, hdup, hΛ, hcheck⟩ := hsafe
    intro t hin
    cases t with
    | val v => trivial
    | var x => exact checkTerms_dom hcheck hin
  | pure p =>
    cases p with
    | term t =>
      cases t with
      | var x => exact hsafe.elim
      | val v => trivial
    | unOp op p => exact hsafe.elim
    | binOp op p₁ p₂ => exact hsafe.elim
  | _ => exact hsafe.elim

theorem safeMain_closed {Λ : Library} {e : Expr} {τ : Ty}
    (hmain : SafeMain Λ e τ) : e.ClosedProgram :=
  safeProgram_closed hmain

end RUXt
