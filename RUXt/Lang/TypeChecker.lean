/-
Port of `theories/model/typechecker.v`: function type signatures and safe
programs.
-/
import RUXt.Lang.Library

namespace RUXt

/-! ### Base types -/

/-- `val_type`. -/
def Val.baseTy : Val → BaseType
  | .int _ => .int
  | .bool _ => .bool
  | .loc _ => .loc
  | .unit => .unit

def Val.ty : Val → Ty
  | v => .base v.baseTy


/-! ### Typed variable contexts -/

/-- Typed variable contexts. -/
abbrev VarCtx := PMap PVar Ty

/-- `cons_var_ctx`. -/
def consVarCtx (xs : List PVar) (τs : List Ty) : VarCtx :=
  (xs.zip τs).foldr (fun xτ m => m.insert xτ.1 xτ.2) ∅

/-- `insert_var_ctx`. -/
theorem insert_var_ctx {xs : List PVar} {τs : List Ty} (x : PVar) (τ : Ty)
    (_ : xs.length = τs.length) :
    (consVarCtx xs τs).insert x τ = consVarCtx (x :: xs) (τ :: τs) := rfl

/-- `lookup_var_ctx_None`. -/
theorem lookup_var_ctx_none {xs : List PVar} {τs : List Ty} {x : PVar}
    (hlen : xs.length = τs.length) (hnin : x ∉ xs) :
    consVarCtx xs τs x = none := by
  induction xs generalizing τs with
  | nil => rfl
  | cons y ys ih =>
    cases τs with
    | nil => simp at hlen
    | cons τ τs =>
      simp only [List.mem_cons, not_or] at hnin
      show PMap.insert y τ (consVarCtx ys τs) x = none
      rw [PMap.insert_apply_ne _ _ hnin.1]
      exact ih (by simpa using hlen) hnin.2

private theorem foldr_insert_comm (l : List (PVar × Ty)) (x : PVar) (τ : Ty)
    (m : VarCtx) (hx : ∀ p ∈ l, p.1 ≠ x) :
    l.foldr (fun xτ m => m.insert xτ.1 xτ.2) (m.insert x τ)
      = (l.foldr (fun xτ m => m.insert xτ.1 xτ.2) m).insert x τ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    rw [ih fun q hq => hx q (List.mem_cons_of_mem p hq),
      PMap.insert_comm (hx p List.mem_cons_self)]

/-- `reverse_var_ctx`. -/
theorem reverse_var_ctx {xs : List PVar} {τs : List Ty}
    (hlen : xs.length = τs.length) (hdup : xs.Nodup) :
    consVarCtx xs τs = consVarCtx xs.reverse τs.reverse := by
  induction xs generalizing τs with
  | nil => rfl
  | cons x xs ih =>
    cases τs with
    | nil => simp at hlen
    | cons τ τs =>
      obtain ⟨hx, hdup'⟩ := List.nodup_cons.mp hdup
      have hlen' : xs.length = τs.length := by simpa using hlen
      show PMap.insert x τ (consVarCtx xs τs) = _
      rw [ih hlen' hdup']
      simp only [List.reverse_cons]
      unfold consVarCtx
      rw [List.zip_append (by simpa using hlen'), List.foldr_append]
      exact (foldr_insert_comm _ x τ ∅ fun p hp h =>
        hx (h ▸ List.mem_reverse.mp (List.of_mem_zip hp).1)).symm

/-! ### Well-typed terms -/

/-- `check_term`: a term is a value of the right base type or a well-typed
variable. -/
def checkTerm (𝕍 : VarCtx) (t : Term) (τ : Ty) : Bool :=
  match t with
  | .var x => 𝕍 x = some τ
  | .val v => Ty.base v.baseTy = τ

/-- `check_terms`. -/
def checkTerms (𝕍 : VarCtx) : List Term → List Ty → Bool
  | [], [] => Bool.true
  | t :: ts, τ :: τs => checkTerm 𝕍 t τ && checkTerms 𝕍 ts τs
  | _, _ => Bool.false

/-- `check_terms_subseteq`. -/
theorem checkTerms_subset {𝕍 𝕍' : VarCtx} {ts : List Term} {τs : List Ty}
    (hcheck : checkTerms 𝕍' ts τs = Bool.true) (hsub : 𝕍' ⊆ 𝕍) :
    checkTerms 𝕍 ts τs = Bool.true := by
  induction ts generalizing τs with
  | nil => cases τs <;> simp_all [checkTerms]
  | cons t ts ih =>
    cases τs with
    | nil => simp_all [checkTerms]
    | cons τ τs =>
      simp only [checkTerms, Bool.and_eq_true] at hcheck ⊢
      refine ⟨?_, ih hcheck.2⟩
      cases t with
      | val v => exact hcheck.1
      | var x =>
        simp only [checkTerm, decide_eq_true_eq] at hcheck ⊢
        exact PMap.subset_apply hsub hcheck.1

/-- `check_terms_cons`. -/
theorem checkTerms_consVarCtx {xs : List PVar} {τs : List Ty}
    (hlen : xs.length = τs.length) (hdup : xs.Nodup) :
    checkTerms (consVarCtx xs τs) (Term.ofVars xs) τs = Bool.true := by
  induction xs generalizing τs with
  | nil => cases τs <;> simp_all [checkTerms, Term.ofVars]
  | cons x xs ih =>
    cases τs with
    | nil => simp at hlen
    | cons τ τs =>
      obtain ⟨hnin, hdup'⟩ := List.nodup_cons.mp hdup
      have hlen' : xs.length = τs.length := by simpa using hlen
      rw [← insert_var_ctx x τ hlen']
      simp only [Term.ofVars_cons, checkTerms, Bool.and_eq_true]
      constructor
      · simp [checkTerm]
      · refine checkTerms_subset (ih hlen' hdup') ?_
        intro a b hab
        by_cases hax : a = x
        · subst hax
          rw [lookup_var_ctx_none hlen' hnin] at hab
          exact absurd hab (by simp)
        · rwa [PMap.insert_apply_ne _ _ hax]

/-- `check_terms_dom`. -/
theorem checkTerms_dom {𝕍 : VarCtx} {ts : List Term} {τs : List Ty} {x : PVar}
    (hcheck : checkTerms 𝕍 ts τs = Bool.true) (hin : Term.var x ∈ ts) :
    x ∈ 𝕍.dom := by
  induction ts generalizing τs with
  | nil => simp at hin
  | cons t ts ih =>
    cases τs with
    | nil => simp_all [checkTerms]
    | cons τ τs =>
      simp only [checkTerms, Bool.and_eq_true] at hcheck
      rcases List.mem_cons.mp hin with rfl | hin'
      · have := hcheck.1
        simp only [checkTerm, decide_eq_true_eq] at this
        exact PMap.mem_dom.mpr ⟨τ, this⟩
      · exact ih hcheck.2 hin'

/-! ### Safe programs -/

/-- `safe_program`: a safe program only has calls to the library. -/
def safeProgram (𝕍 : VarCtx) (Λ : Library) (e : Expr) : Option Ty :=
  match e with
  | .letIn bx e₁ e₂ =>
      match safeProgram 𝕍 Λ e₁ with
      | some τ =>
          match bx with
          | .named x => safeProgram (𝕍.insert x τ) Λ e₂
          | .anon => safeProgram 𝕍 Λ e₂
      | none => none
  | .call f ts =>
      match Λ.get f with
      | some ⟨xs, _, τ, _⟩ => if checkTerms 𝕍 ts (xs.map Prod.snd) then some τ else none
      | none => none
  | .pure (.term (.val v)) => some (.base v.baseTy)
  | _ => none

/-- `safe_main`: a main program is a safe program with no free variables. -/
def safeMain (Λ : Library) (e : Expr) : Option Ty := safeProgram ∅ Λ e

/-- `safe_program_subseteq`. -/
theorem safeProgram_subset {𝕍 𝕍' : VarCtx} {Λ : Library} {e : Expr} {τ : Ty}
    (hsafe : safeProgram 𝕍' Λ e = some τ) (hsub : 𝕍' ⊆ 𝕍) :
    safeProgram 𝕍 Λ e = some τ := by
  induction e generalizing 𝕍 𝕍' τ with
  | letIn bx e₁ e₂ ih₁ ih₂ =>
    simp only [safeProgram] at hsafe ⊢
    cases h₁ : safeProgram 𝕍' Λ e₁ with
    | none => simp [h₁] at hsafe
    | some τ₁ =>
      simp only [h₁] at hsafe
      simp only [ih₁ h₁ hsub]
      cases bx with
      | anon => exact ih₂ hsafe hsub
      | named x => exact ih₂ hsafe (PMap.insert_mono _ _ hsub)
  | call f ts =>
    simp only [safeProgram] at hsafe ⊢
    cases hΛ : Λ.get f with
    | none => simp [hΛ] at hsafe
    | some s =>
      obtain ⟨τs, τ'⟩ := s
      simp only [hΛ] at hsafe ⊢
      split at hsafe
      case isTrue hcheck => rwa [if_pos (checkTerms_subset hcheck hsub)]
      case isFalse => exact absurd hsafe (by simp)
  | pure p =>
    cases p with
    | term t => cases t <;> simp_all [safeProgram]
    | unOp op p => simp_all [safeProgram]
    | binOp op p₁ p₂ => simp_all [safeProgram]
  | _ => simp_all [safeProgram]

/-- `safe_main_Some`. -/
theorem safeMain_some {Λ : Library} {e : Expr} {τ : Ty} (𝕍 : VarCtx)
    (hmain : safeMain Λ e = some τ) :
    safeProgram 𝕍 Λ e = some τ :=
  safeProgram_subset hmain (PMap.empty_subset 𝕍)

/-- `safe_call`. -/
theorem safe_call {Λ : Library} {f : Fid} {xs e τ hdup}
   (htype : Λ.get f = some ⟨xs, e, τ, hdup⟩) :
    safeProgram (consVarCtx (xs.map Prod.fst) (xs.map Prod.snd))
      Λ (.call f (Term.ofVars (xs.map Prod.fst))) = some τ := by
  simp [safeProgram, htype]
  rw [checkTerms_consVarCtx _ hdup]; simp

/-- `safe_program_closed`. -/
theorem safeProgram_closed {𝕍 : VarCtx} {Λ : Library} {e : Expr} {τ : Ty}
    (hsafe : safeProgram 𝕍 Λ e = some τ) :
    e.Closed 𝕍.dom := by
  induction e generalizing 𝕍 τ with
  | letIn bx e₁ e₂ ih₁ ih₂ =>
    simp only [safeProgram] at hsafe
    cases h₁ : safeProgram 𝕍 Λ e₁ with
    | none => simp [h₁] at hsafe
    | some τ₁ =>
      simp only [h₁] at hsafe
      refine ⟨ih₁ h₁, ?_⟩
      cases bx with
      | anon => exact ih₂ hsafe
      | named x =>
        have := ih₂ hsafe
        rw [PMap.dom_insert] at this
        rwa [Set.union_comm] at this
  | call f ts =>
    simp only [safeProgram] at hsafe
    cases hΛ : Λ.get f with
    | none => simp [hΛ] at hsafe
    | some s =>
      obtain ⟨τs, τ'⟩ := s
      simp only [hΛ] at hsafe
      split at hsafe
      case isFalse => exact absurd hsafe (by simp)
      case isTrue hcheck =>
        intro t hin
        cases t with
        | val v => trivial
        | var x => exact checkTerms_dom hcheck hin
  | pure p =>
    cases p with
    | term t =>
      cases t with
      | var x => simp_all [safeProgram]
      | val v => trivial
    | unOp op p => simp_all [safeProgram]
    | binOp op p₁ p₂ => simp_all [safeProgram]
  | _ => simp_all [safeProgram]

/-- `safe_main_closed`. -/
theorem safeMain_closed {Λ : Library} {e : Expr} {τ : Ty}
    (hmain : safeMain Λ e = some τ) :
    e.ClosedProgram := by
  have := safeProgram_closed hmain
  rwa [PMap.dom_empty] at this

end RUXt
