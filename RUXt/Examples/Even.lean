import RUXt.Model.Refute
import RUXt.Examples.RISL

namespace RUXt

/-!
# The `Even` library and its type unsoundness

This file formalises a small (unsound) Rust library for even numbers and shows, via
the refutation algorithm of `RUXt/Model/Refute.lean`, that the library is *inadequate*:
it has a well-typed main program whose execution exhibits undefined behaviour. -/

/-- Creates an even number from an integer. -/
def newBody : Expr :=
  .pure (.add (.var "n") (.minus (.mod (.var "n") (.int 2))))
/-- Increments its input number. -/
def succBody : Expr :=
  .pure (.add (.var "x") (.int 1))
/-- Computes the next even number. -/
def nextBody : Expr :=
  .letIn (.named "y") (.call "succ" [.var "x"]) (.call "succ" [.var "y"])
/-- Checks whether a pure expression is an even number. -/
abbrev isEven (p : Pure) : Pure :=
  .eq (.mod p (.int 2)) (.int 0)
/-- Performs no operation on even inputs, exhibits UB on odd inputs. -/
def noopBody : Expr :=
  .choice
    (.letIn (.named "g") (.pure (isEven (.var "x")))
      (.letIn .anon (.assume (.var "g")) .unit))
    (.letIn (.named "g") (.pure (.not (isEven (.var "x"))))
      (.letIn .anon (.assume (.var "g")) .error))

/-- `i32` is modelled as the base type `int`. -/
abbrev IntTy : Ty := .base .int
/-- The base type `unit`. -/
abbrev UnitTy : Ty := .base .unit
/-- The custom struct type `Even`. -/
abbrev EvenTy : Ty := .custom "Even"
/-- The `Even` library. -/
noncomputable def evenLib : Library := fun f =>
  if f = "new" then
    Part.some ⟨[("n", IntTy)], newBody, EvenTy, by decide⟩
  else if f = "succ" then
    Part.some ⟨[("x", EvenTy)], succBody, EvenTy, by decide⟩
  else if f = "next" then
    Part.some ⟨[("x", EvenTy)], nextBody, EvenTy, by decide⟩
  else if f = "noop" then
    Part.some ⟨[("x", EvenTy)], noopBody, UnitTy, by decide⟩
  else Part.none

theorem evenLib_new :
    evenLib.MapsTo "new" ⟨[("n", IntTy)], newBody, EvenTy, by decide⟩ := by
  simp [Library.MapsTo, evenLib]
theorem evenLib_succ :
    evenLib.MapsTo "succ" ⟨[("x", EvenTy)], succBody, EvenTy, by decide⟩ := by
  simp [Library.MapsTo, evenLib]
theorem evenLib_noop :
    evenLib.MapsTo "noop" ⟨[("x", EvenTy)], noopBody, UnitTy, by decide⟩ := by
  simp [Library.MapsTo, evenLib]

/-! ### Summaries -/

/-- Construct a specification context for the function being executed. -/
abbrev SpecCtx.fromPicks (ςs : SummPicks) (f : Fid)
  (ε : LExit) (Φ : Val → Tele.triple ςs -t> Asrt) : SpecCtx :=
  SpecCtx.update ⟨_, mergeVals ςs, mergePosts ςs, ε, Φ⟩ f ∅

/-- Picks for `new`: the base `int` summary. -/
def ςs1 : SummPicks := [(IntTy, baseSummary.{0} .int)]
/-- Post of the `even` summary: `new` maps `.int z` to the even `.int (z-z%2)`. -/
def Φeven : Val → Tele.triple ςs1 -t> Asrt := fun r v₀ z =>
  ⌞ v₀ = .int z ∧ r = .int (z - z.tmod 2) ⌟
/-- The (correct) summary for `Even`, obtained from `new`. -/
def evenSumm : Summary.{0} := ⟨Tele.triple ςs1, Φeven, witness "new" ["n"] ςs1⟩
/-- Context after adding the even summary. -/
def S1 : SummCtx := SummCtx.update baseSummCtx EvenTy evenSumm
/-- Refutation step 1: `new` builds the (correct) even summary for `Even`. -/
theorem tryRefute_even : TryRefute evenLib baseSummCtx (.inl S1) := by
  refine ⟨ςs1, ?summIncl, "new", ["n"], EvenTy, .lok, Φeven, ?derivPost,
    .int 0, ⟨.int 0, 0, .unit⟩, ?satPost, rfl, rfl⟩
  case summIncl =>
    intro τ ς h
    simp only [ςs1, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [baseSummCtx, SummCtx.update]
  case satPost =>
    exact ⟨∅, rfl, rfl, by norm_num [Int.tmod]⟩
  case derivPost =>
    refine ⟨[("n", IntTy)], newBody, by decide, evenLib_new, rfl, rfl, ?_⟩
    -- Select RISL as our logic for executing the function call
    refine ⟨risl, SpecCtx.fromPicks ςs1 "new" .lok Φeven,
      ⟨.update .empty rfl evenLib_new ?_, .call (by simp [SpecCtx.update_apply])⟩⟩
    -- Prove triple for the function body
    refine
      -- Commute .emp in precondition, evaluate modulo operation in postcondition
      .cons id (fun _ => List.Subset.refl _) ?consComm ?consEval (fun _ => rfl)
      -- Frame all .int equalities
      (.frame (tt := .triple ςs1)
        (R := fun v₀ z =>
          ⌞ v₀ = .int z ⌟)
      -- Evaluate modulo operation as a pure expression
      (.reindex (tt := [tele (_ : Pure)]) (tt' := .triple ςs1)
        (fun ⟨v₀, _⟩ => ⟨.add (.val v₀) (.minus (.mod (.val v₀) (.int 2))), .unit⟩) .pure))
    case consEval =>
      rintro _ ⟨_, _, _, _⟩ _ ⟨rfl, hv₀, rfl⟩
      simp at hv₀; subst hv₀
      exact ⟨∅, ∅, by simp, by simp,
        ⟨rfl, rfl⟩,
        ⟨rfl, rfl⟩⟩
    case consComm =>
      exact fun _ _ => hStar_comm.mp

/-- Picks for `succ`: the even `Even` summary. -/
def ςs2 : SummPicks := [(EvenTy, evenSumm)]
/-- Post of the `odd` summary: `succ` maps the even `.int (z-z%2)` to the odd
`.int ((z-z%2)+1)`. -/
def Φodd : Val → Tele.triple ςs2 -t> Asrt := fun r v₁ v₀ z =>
  ⌞ v₀ = .int z ∧ v₁ = .int (z - z.tmod 2) ∧ r = .int ((z - z.tmod 2) + 1) ⌟
/-- The *unsound* odd summary for `Even`, obtained from `succ`. -/
def oddSumm : Summary.{0} := ⟨Tele.triple ςs2, Φodd, witness "succ" ["x"] ςs2⟩
/-- Context after adding the odd summary. -/
def S2 : SummCtx := SummCtx.update S1 EvenTy oddSumm
/-- Refutation step 2: `succ` builds the *unsound* odd summary for `Even`. -/
theorem tryRefute_odd : TryRefute evenLib S1 (.inl S2) := by
  refine ⟨ςs2, ?summIncl, "succ", ["x"], EvenTy, .lok, Φodd, ?derivPost,
    .int 1, ⟨.int 0, .int 0, 0, .unit⟩, ?satPost, rfl, rfl⟩
  case summIncl =>
    intro τ ς h
    simp only [ςs2, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [S1, SummCtx.update]
  case satPost =>
    exact ⟨∅, rfl, rfl, by norm_num [Int.tmod]⟩
  case derivPost =>
    refine ⟨[("x", EvenTy)], succBody, by decide, evenLib_succ, rfl, rfl, ?_⟩
    -- Select RISL as our logic for executing the function call
    refine ⟨risl, SpecCtx.fromPicks ςs2 "succ" .lok Φodd,
      ⟨.update .empty rfl evenLib_succ ?_, .call (by simp [SpecCtx.update_apply])⟩⟩
    -- Prove triple for the function body
    refine
      -- Commute .emp in precondition, evaluate increment in postcondition
      .cons id (fun _ => List.Subset.refl _) ?consComm ?consEval (fun _ => rfl)
      -- Frame all .int equalities
      (.frame (tt := .triple ςs2)
        (R := fun v₁ v₀ z =>
          ⌞ v₀ = .int z ∧ v₁ = .int (z - z.tmod 2) ⌟)
      -- Evaluate increment as a pure expression
      (.reindex (tt := [tele (_ : Pure)]) (tt' := .triple ςs2)
        (fun ⟨v₁, _⟩ => ⟨.add (.val v₁) (.int 1), .unit⟩) .pure))
    case consEval =>
      rintro _ ⟨_, _, _, _⟩ _ ⟨rfl, hv₀, hv₁, rfl⟩
      simp at hv₀ hv₁; subst hv₀ hv₁
      exact ⟨∅, ∅, by simp, by simp,
        ⟨rfl, rfl⟩,
        ⟨rfl, rfl, rfl⟩⟩
    case consComm =>
      exact fun _ _ => hStar_comm.mp

/-- Picks for `noop`: the odd `Even` summary. -/
def ςs3 : SummPicks := [(EvenTy, oddSumm)]
/-- Post of the `noop` call: it reaches an error state for the odd input
`.int ((z-z%2)+1)`, returning .unit -/
def Φnoop : Val → Tele.triple ςs3 -t> Asrt := fun r v₂ v₁ v₀ z =>
  ⌞ v₀ = .int z ∧ v₁ = .int (z - z.tmod 2) ∧ v₂ = .int (z - z.tmod 2 + 1) ∧ r = .unit ⌟
/-- The witnessing program: `noop(succ(new(0)))` in let-normal form. -/
def witnessExpr : Expr :=
  (witness "noop" ["x"] ςs3).apply ⟨.int 1, .int 0, .int 0, 0, .unit⟩
/-- Refutation step 3: `noop` on the odd summary reaches a non-`ok` state, so it
yields the type-unsoundness witness `witnessExpr`. -/
theorem tryRefute_noop : TryRefute evenLib S2 (.inr witnessExpr) := by
  refine ⟨ςs3, ?summIncl, "noop", ["x"], UnitTy, .lerr, Φnoop, ?derivPost,
    .unit, ⟨.int 1, .int 0, .int 0, 0, .unit⟩, ?satPost, by simp, rfl⟩
  case summIncl =>
    intro τ ς h
    simp only [ςs3, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [S2, SummCtx.update]
  case satPost =>
    exact ⟨∅, rfl, rfl, by norm_num [Int.tmod]⟩
  case derivPost =>
    refine ⟨[("x", EvenTy)], noopBody, by decide, evenLib_noop, rfl, rfl, ?_⟩
    -- Select RISL as our logic for executing the function call
    refine ⟨risl, SpecCtx.fromPicks ςs3 "noop" .lerr Φnoop,
      ⟨.update .empty rfl evenLib_noop ?_, .call (by simp [SpecCtx.update_apply])⟩⟩
    -- Prove triple for the function body
    refine
      -- Choose the error branch
      .choice (tt := .triple ςs3)
        (e₁ := fun v₂ _ _ _ => .letIn (.named "g") (.pure (isEven (.val v₂)))
          (.letIn .anon (.assume (.var "g")) .unit))
        (e₂ := fun v₂ _ _ _ => .letIn (.named "g") (.pure (.not (isEven (.val v₂))))
          (.letIn .anon (.assume (.var "g")) .error))
        (Or.inr rfl)
      -- Commute .emp in precondition, evaluate guard to true in postcondition
      (.cons id (fun _ => List.Subset.refl _) ?consComm ?consEval (fun _ => rfl)
      -- Frame all .int equalities
      (.frame (tt := .triple ςs3)
        (R := fun v₂ v₁ v₀ z =>
          ⌞ v₀ = .int z ∧ v₁ = .int (z - z.tmod 2) ∧ v₂ = .int (z - z.tmod 2 + 1) ⌟)
        (Φ := fun r v₂ _ _ _ => ⌞ r = .unit ⌟ ∗
          ⌞ some (.bool true) = Pure.eval (.not (isEven (.val v₂))) ⌟)
      -- Evaluate let-binding for the guard
      (.letIn (tt:= .triple ςs3)
        (e₂ := fun _ _ _ _ => .letIn .anon (.assume (.var "g")) .error)
      -- Evaluate guard as a pure expression
      (.reindex (tt := [tele (_ : Pure)]) (tt' := .triple ςs3)
        (fun ⟨v₂, _⟩ => ⟨.not (isEven (.val v₂)), .unit⟩) .pure)
      -- Add .emp to precondition for framing
      (.cons id (fun _ => List.Subset.refl _) ?consEmp (fun _ _ _ hh => hh) (fun _ => rfl)
      -- Frame the guard evaluation
      (.frame (tt := .triple ςs3)
        (R := fun v₂ _ _ _ =>
          ⌞ some (.bool true) = Pure.eval (.not (isEven (.val v₂))) ⌟)
      -- Evaluate let-binding for assume
      (.letIn (v := .unit)
      -- Evaluate assume
      (.reindex (tt := [tele]) (fun _ => .unit) .assume)
      -- Remove unit equality from precondition
      (.cons id (fun _ => List.Subset.refl _) ?consUnit (fun _ _ _ hh => hh) (fun _ => rfl)
      -- Evaluate error
      (.reindex (tt := [tele]) (fun _ => .unit) .error))))))))
    case consEval =>
      rintro _ ⟨_, _, _, z, _⟩ h ⟨rfl, hv₀, hv₁, hv₂, rfl⟩
      simp at hv₀ hv₁ hv₂; subst hv₀ hv₁ hv₂
      refine ⟨∅, ∅, by simp, by simp,
        ⟨∅, ∅, by simp, by simp, ⟨by simp, ?_⟩⟩,
        ⟨rfl, rfl, rfl, rfl⟩⟩
      simp [Pure.eval, UnOp.eval, BinOp.eval]
      rw [← Int.dvd_iff_tmod_eq_zero]
      have := Int.mul_tdiv_add_tmod z 2
      omega
    case consComm =>
      exact fun _ _ => hStar_comm.mp
    case consEmp =>
      exact fun _ h hh => hEmpty_left _ h (hStar_comm.mp hh)
    case consUnit =>
      exact fun _ _ hh => ⟨hh, by simp⟩

/-! ### Well-formed summary context and inadequacy -/

/-- **The `Even` library is inadequate**: `noop(succ(new(0)))` is a well-typed
main program that exhibits undefined behaviour. -/
theorem even_inadequate : Inadequate evenLib witnessExpr :=
  inadequacy ⟨S2, .cons (.cons .nil tryRefute_even) tryRefute_odd, tryRefute_noop⟩

end RUXt
