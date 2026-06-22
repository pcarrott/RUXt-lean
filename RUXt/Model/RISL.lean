/-
Port of `theories/model/risl.v`: RISL proof rules, instantiation as UX logic.
-/
import RUXt.Lang.Lang
import RUXt.Lang.Semantics
import RUXt.Lang.Assertion
import RUXt.Model.Logic

namespace RUXt

open scoped PMap

/-! ### Function specifications -/

/-- `fun_spec` (Rocq notation `⌈(vs) P | ε, Q⌉`). -/
structure FunSpec : Type 1 where
  vals : List Val
  pre : Asrt
  tag : Exit
  post : Asrt

/-- Specification contexts. In the Rocq development these are
`gmap string (list fun_spec)` accessed exclusively through the total lookup
`!!!` (defaulting to `[]`); total functions into lists are the faithful
counterpart. -/
def SpecCtx := String → List FunSpec

instance : EmptyCollection SpecCtx := ⟨fun _ => []⟩

@[simp] theorem SpecCtx.empty_apply (f : String) : (∅ : SpecCtx) f = [] := rfl

/-- `update` (adds one specification for `f`, as `partial_alter (spec_cons s)`
does). -/
def SpecCtx.update (s : FunSpec) (f : String) (Γ : SpecCtx) : SpecCtx :=
  Function.update Γ f (s :: Γ f)

/-- `subseteq` (`Γ [⊆] Γ'`). -/
def SpecCtx.Subseteq (Γ Γ' : SpecCtx) : Prop := ∀ f, Γ f ⊆ Γ' f

@[inherit_doc] scoped infix:50 " [⊆] " => SpecCtx.Subseteq

/-- `lookup_total_update`. -/
theorem SpecCtx.update_apply (Γ : SpecCtx) (f : String) (s : FunSpec) :
    Γ.update s f f = s :: Γ f :=
  Function.update_self ..

/-- `lookup_total_update_ne`. -/
theorem SpecCtx.update_apply_ne (Γ : SpecCtx) {f g : String} (s : FunSpec) (h : f ≠ g) :
    Γ.update s f g = Γ g :=
  Function.update_of_ne (Ne.symm h) ..

/-! ### Frameable assertions -/

/-- `frameable`. -/
def Frameable (ε : Exit) (R : Asrt) : Prop :=
  match ε with
  | .miss l => l.2 = 0 ∧ ¬ sat (⌜Asrt.ex fun bv => Asrt.single l bv⌝ ∧ₕ R)
  | _ => True

/-- `frameable_heap`. -/
theorem Frameable.not_mem_dom {l : Loc} {R : Asrt} (hframe : Frameable (.miss l) R) :
    ∀ h, hprop h R → l.1 ∈ h.dom → False := by
  obtain ⟨hofs, hnsat⟩ := hframe
  intro h hR hin
  apply hnsat
  refine ⟨h, ?_, hR⟩
  obtain ⟨bv, hbv⟩ := PMap.mem_dom.mp hin
  exact ⟨PMap.singleton l.1 bv, PMap.delete l.1 h,
    PMap.eq_singleton_union_delete hbv, PMap.disjoint_singleton_delete h l.1 bv,
    ⟨bv, rfl, hofs⟩, trivial⟩

/-! ### Proof rules -/

/-- The RISL proof rules (`wf_spec`, `Γ ⊢ ⌈P⌉ e ⌈ε, Q⌉`). -/
inductive WfSpec : SpecCtx → Asrt → Expr → Exit → Asrt → Prop
  | value {Γ : SpecCtx} {v : Val} :
      WfSpec Γ .emp (.pure (.val v)) (.ok v) .emp
  | minus {Γ : SpecCtx} {p : Pure} {z : ℤ} :
      WfSpec Γ .emp (.pure p) (.ok (.int z)) .emp →
      WfSpec Γ .emp (.pure (.minus p)) (.ok (.int (-z))) .emp
  | not {Γ : SpecCtx} {p : Pure} {b : Bool} :
      WfSpec Γ .emp (.pure p) (.ok (.bool b)) .emp →
      WfSpec Γ .emp (.pure (.not p)) (.ok (.bool !b)) .emp
  | add {Γ : SpecCtx} {p₁ p₂ : Pure} {z₁ z₂ : ℤ} :
      WfSpec Γ .emp (.pure p₁) (.ok (.int z₁)) .emp →
      WfSpec Γ .emp (.pure p₂) (.ok (.int z₂)) .emp →
      WfSpec Γ .emp (.pure (.add p₁ p₂)) (.ok (.int (z₁ + z₂))) .emp
  | le {Γ : SpecCtx} {p₁ p₂ : Pure} {z₁ z₂ : ℤ} :
      WfSpec Γ .emp (.pure p₁) (.ok (.int z₁)) .emp →
      WfSpec Γ .emp (.pure p₂) (.ok (.int z₂)) .emp →
      WfSpec Γ .emp (.pure (.le p₁ p₂)) (.ok (.bool (decide (z₁ ≤ z₂)))) .emp
  | assume {Γ : SpecCtx} :
      WfSpec Γ .emp (.assume .true) (.ok .unit) .emp
  | error {Γ : SpecCtx} :
      WfSpec Γ .emp .error .err .emp
  | letIn {Γ : SpecCtx} {x : Binder} {e₁ e₂ : Expr} {P Q R : Asrt} {v : Val} {ε : Exit} :
      WfSpec Γ P e₁ (.ok v) R → WfSpec Γ R (e₂.subst x v) ε Q →
      WfSpec Γ P (.letIn x e₁ e₂) ε Q
  | letCut {Γ : SpecCtx} {x : Binder} {e₁ e₂ : Expr} {P Q : Asrt} {ε : Exit} :
      WfSpec Γ P e₁ ε Q → (¬ ∃ v, ε = .ok v) →
      WfSpec Γ P (.letIn x e₁ e₂) ε Q
  | choice {Γ : SpecCtx} {eᵢ e₁ e₂ : Expr} {P Q : Asrt} {ε : Exit} :
      WfSpec Γ P eᵢ ε Q → (eᵢ = e₁ ∨ eᵢ = e₂) →
      WfSpec Γ P (.choice e₁ e₂) ε Q
  | alloc {Γ : SpecCtx} {l : Loc} :
      WfSpec Γ .emp (.alloc (.int 1)) (.ok (.loc l)) (l ↦?)
  | free {Γ : SpecCtx} {l : Loc} {v : Val} :
      WfSpec Γ (l ↦ v) (.free (.loc l)) (.ok .unit) (l ↦∅)
  | freeUninit {Γ : SpecCtx} {l : Loc} :
      WfSpec Γ (l ↦?) (.free (.loc l)) (.ok .unit) (l ↦∅)
  | freeFreed {Γ : SpecCtx} {l : Loc} :
      WfSpec Γ (l ↦∅) (.free (.loc l)) .err (l ↦∅)
  | freeEmp {Γ : SpecCtx} {l : Loc} :
      WfSpec Γ .emp (.free (.loc l)) (.miss l) .emp
  | store {Γ : SpecCtx} {l : Loc} {v v' : Val} :
      WfSpec Γ (l ↦ v') (.store (.loc l) (.val v)) (.ok .unit) (l ↦ v)
  | storeUninit {Γ : SpecCtx} {l : Loc} {v : Val} :
      WfSpec Γ (l ↦?) (.store (.loc l) (.val v)) (.ok .unit) (l ↦ v)
  | storeFreed {Γ : SpecCtx} {l : Loc} {v : Val} :
      WfSpec Γ (l ↦∅) (.store (.loc l) (.val v)) .err (l ↦∅)
  | storeEmp {Γ : SpecCtx} {l : Loc} {v : Val} :
      WfSpec Γ .emp (.store (.loc l) (.val v)) (.miss l) .emp
  | load {Γ : SpecCtx} {l : Loc} {v : Val} :
      WfSpec Γ (l ↦ v) (.load (.loc l)) (.ok v) (l ↦ v)
  | loadUninit {Γ : SpecCtx} {l : Loc} :
      WfSpec Γ (l ↦?) (.load (.loc l)) .err (l ↦?)
  | loadFreed {Γ : SpecCtx} {l : Loc} :
      WfSpec Γ (l ↦∅) (.load (.loc l)) .err (l ↦∅)
  | loadEmp {Γ : SpecCtx} {l : Loc} :
      WfSpec Γ .emp (.load (.loc l)) (.miss l) .emp
  | frame {Γ : SpecCtx} {e : Expr} {P Q R : Asrt} {ε : Exit} :
      WfSpec Γ P e ε Q → Frameable ε R →
      WfSpec Γ (P ∗ R) e ε (Q ∗ R)
  | disj {Γ : SpecCtx} {e : Expr} {P₁ P₂ Q₁ Q₂ : Asrt} {ε : Exit} :
      WfSpec Γ P₁ e ε Q₁ → WfSpec Γ P₂ e ε Q₂ →
      WfSpec Γ (P₁ ∨ₕ P₂) e ε (Q₁ ∨ₕ Q₂)
  | cons {Γ Γ' : SpecCtx} {e : Expr} {P P' Q Q' : Asrt} {ε : Exit} :
      Γ' [⊆] Γ → (⊨ (P' →ₕ P)) → (⊨ (Q →ₕ Q')) → WfSpec Γ' P' e ε Q' →
      WfSpec Γ P e ε Q
  | exists' {Γ : SpecCtx} {e : Expr} {P Q : Asrt} {ε : Exit} (X : Type) :
      WfSpec Γ P e ε Q →
      WfSpec Γ (.ex fun _ : X => P) e ε (.ex fun _ : X => Q)
  | call {Γ : SpecCtx} {f : String} {vs : List Val} {P Q : Asrt} {ε : Exit} :
      (⟨vs, P, ε, Q⟩ : FunSpec) ∈ Γ f →
      WfSpec Γ P (.call f (Term.ofVals vs)) ε Q

@[inherit_doc] scoped notation:50 Γ:51 " ⊢ " "⌈" P "⌉ " e:51 " ⌈" ε ", " Q "⌉" =>
  WfSpec Γ P e ε Q

/-! ### Well-formed specification contexts -/

/-- `wf_spec_ctx` (`γ ≺ₛ Γ`). -/
inductive WfSpecCtx (γ : ImplCtx) : SpecCtx → Prop
  | empty :
      WfSpecCtx γ ∅
  | update {Γ Γ' : SpecCtx} {P Q : Asrt} {ε : Exit} {f : String} {xs : List String}
      {e : Expr} {vs : List Val} :
      WfSpecCtx γ Γ → γ f = some ⟨xs, e⟩ →
      (Γ ⊢ ⌈P⌉ (e.substs xs (Term.ofVals vs)) ⌈ε, Q⌉) →
      Γ' = Γ.update ⟨vs, P, ε, Q⟩ f →
      WfSpecCtx γ Γ'

@[inherit_doc] scoped infix:50 " ≺ₛ " => WfSpecCtx

/-! ### Soundness -/

/-- `valid_spec_ctx`. -/
def ValidSpecCtx (γ : ImplCtx) (Γ : SpecCtx) : Prop :=
  ∀ f vs P Q ε, (⟨vs, P, ε, Q⟩ : FunSpec) ∈ Γ f →
    ∃ xs e, γ f = some ⟨xs, e⟩ ∧ UXFrameTriple γ (e.substs xs (Term.ofVals vs)) P Q ε

/-- `valid_spec`. -/
def ValidSpec (Γ : SpecCtx) (e : Expr) (P Q : Asrt) (ε : Exit) : Prop :=
  ∀ γ, ValidSpecCtx γ Γ → UXFrameTriple γ e P Q ε

/-- `spec_ctx_inclusion`. -/
theorem spec_ctx_inclusion {γ : ImplCtx} {Γ Γ' : SpecCtx}
    (hval : ValidSpecCtx γ Γ) (hsub : Γ' [⊆] Γ) : ValidSpecCtx γ Γ' :=
  fun f vs P Q ε hin => hval f vs P Q ε (hsub f hin)

/-- Soundness of the RISL proof rules (`spec_soundness`). -/
theorem spec_soundness {Γ : SpecCtx} {P : Asrt} {e : Expr} {ε : Exit} {Q : Asrt}
    (hrule : Γ ⊢ ⌈P⌉ e ⌈ε, Q⌉) : ValidSpec Γ e P Q ε := by
  induction hrule with
  | value => exact fun γ _ h' hQ => ⟨h', hQ, .pure rfl⟩
  | minus _ ih =>
    intro γ hval h' hQ
    obtain ⟨h, hP, hstep⟩ := ih γ hval h' hQ
    cases hstep with
    | pure hp => exact ⟨_, hP, .pure (Pure.eval_minus hp)⟩
  | not _ ih =>
    intro γ hval h' hQ
    obtain ⟨h, hP, hstep⟩ := ih γ hval h' hQ
    cases hstep with
    | pure hp => exact ⟨_, hP, .pure (Pure.eval_not hp)⟩
  | add _ _ ih₁ ih₂ =>
    intro γ hval h' hQ
    obtain ⟨h₁, hP₁, hstep₁⟩ := ih₁ γ hval h' hQ
    obtain ⟨h₂, hP₂, hstep₂⟩ := ih₂ γ hval h' hQ
    cases hstep₁ with
    | pure hp₁ =>
      cases hstep₂ with
      | pure hp₂ => exact ⟨_, hP₁, .pure (Pure.eval_add hp₁ hp₂)⟩
  | le _ _ ih₁ ih₂ =>
    intro γ hval h' hQ
    obtain ⟨h₁, hP₁, hstep₁⟩ := ih₁ γ hval h' hQ
    obtain ⟨h₂, hP₂, hstep₂⟩ := ih₂ γ hval h' hQ
    cases hstep₁ with
    | pure hp₁ =>
      cases hstep₂ with
      | pure hp₂ => exact ⟨_, hP₁, .pure (Pure.eval_le hp₁ hp₂)⟩
  | assume => exact fun γ _ h' hQ => ⟨h', hQ, .assume⟩
  | error => exact fun γ _ h' hQ => ⟨h', hQ, .error⟩
  | letIn _ _ ih₁ ih₂ =>
    intro γ hval h' hQ
    obtain ⟨h'', hR, hstep₂⟩ := ih₂ γ hval h' hQ
    obtain ⟨h, hP, hstep₁⟩ := ih₁ γ hval h'' hR
    exact ⟨h, hP, .letIn hstep₁ hstep₂⟩
  | letCut _ hne ih =>
    intro γ hval h' hQ
    obtain ⟨h, hP, hstep⟩ := ih γ hval h' hQ
    exact ⟨h, hP, .letCut hstep hne⟩
  | choice _ hor ih =>
    intro γ hval h' hQ
    obtain ⟨h, hP, hstep⟩ := ih γ hval h' hQ
    exact ⟨h, hP, .choice hstep hor⟩
  | @alloc Γ' l =>
    intro γ _ h' hQ
    simp only [hprop_pointsToUninit] at hQ
    obtain ⟨rfl, hl2⟩ := hQ
    refine ⟨∅, rfl, .alloc (n := 1) rfl (by simp) hl2 ?_⟩
    rw [hl2]
    rfl
  | @free Γ' l v =>
    intro γ _ h' hQ
    simp only [hprop_pointsToFreed] at hQ
    obtain ⟨rfl, hl2⟩ := hQ
    refine ⟨_, ⟨rfl, hl2⟩,
      .free (sz := 1) (bh := PMap.singleton l.2 (.val v)) rfl (by simp) hl2 ?_ ?_⟩
    · intro i hi
      obtain rfl : i = 0 := by omega
      rw [hl2]
      simp
    · exact (PMap.insert_singleton ..).symm
  | @freeUninit Γ' l =>
    intro γ _ h' hQ
    simp only [hprop_pointsToFreed] at hQ
    obtain ⟨rfl, hl2⟩ := hQ
    refine ⟨_, ⟨rfl, hl2⟩,
      .free (sz := 1) (bh := PMap.singleton l.2 .poison) rfl (by simp) hl2 ?_ ?_⟩
    · intro i hi
      obtain rfl : i = 0 := by omega
      rw [hl2]
      simp
    · exact (PMap.insert_singleton ..).symm
  | freeFreed =>
    intro γ _ h' hQ
    simp only [hprop_pointsToFreed] at hQ
    obtain ⟨rfl, hl2⟩ := hQ
    exact ⟨_, ⟨rfl, hl2⟩, .freeErr rfl (by simp)⟩
  | freeEmp =>
    intro γ _ h' hQ
    obtain rfl : h' = ∅ := hQ
    exact ⟨∅, rfl, .freeMiss rfl (by simp)⟩
  | @store Γ' l v v' =>
    intro γ _ h' hQ
    simp only [hprop_pointsTo] at hQ
    obtain ⟨rfl, hl2⟩ := hQ
    refine ⟨_, ⟨rfl, hl2⟩,
      .store (sz := 1) (bh := PMap.singleton l.2 (.val v')) rfl rfl (by simp) (by simp) ?_⟩
    simp [bupdate, hupdate]
  | @storeUninit Γ' l v =>
    intro γ _ h' hQ
    simp only [hprop_pointsTo] at hQ
    obtain ⟨rfl, hl2⟩ := hQ
    refine ⟨_, ⟨rfl, hl2⟩,
      .store (sz := 1) (bh := PMap.singleton l.2 .poison) rfl rfl (by simp) (by simp) ?_⟩
    simp [bupdate, hupdate]
  | storeFreed =>
    intro γ _ h' hQ
    simp only [hprop_pointsToFreed] at hQ
    obtain ⟨rfl, hl2⟩ := hQ
    exact ⟨_, ⟨rfl, hl2⟩, .storeErr rfl (by simp)⟩
  | storeEmp =>
    intro γ _ h' hQ
    obtain rfl : h' = ∅ := hQ
    exact ⟨∅, rfl, .storeMiss rfl (by simp)⟩
  | @load Γ' l v =>
    intro γ _ h' hQ
    simp only [hprop_pointsTo] at hQ
    obtain ⟨rfl, hl2⟩ := hQ
    exact ⟨_, ⟨rfl, hl2⟩,
      .load (sz := 1) (bh := PMap.singleton l.2 (.val v)) rfl (by simp) (by simp)⟩
  | @loadUninit Γ' l =>
    intro γ _ h' hQ
    simp only [hprop_pointsToUninit] at hQ
    obtain ⟨rfl, hl2⟩ := hQ
    exact ⟨_, ⟨rfl, hl2⟩,
      .loadErrBlock (sz := 1) (bh := PMap.singleton l.2 .poison) rfl (by simp) (by simp)⟩
  | loadFreed =>
    intro γ _ h' hQ
    simp only [hprop_pointsToFreed] at hQ
    obtain ⟨rfl, hl2⟩ := hQ
    exact ⟨_, ⟨rfl, hl2⟩, .loadErr rfl (by simp)⟩
  | loadEmp =>
    intro γ _ h' hQ
    obtain rfl : h' = ∅ := hQ
    exact ⟨∅, rfl, .loadMiss rfl (by simp)⟩
  | frame _ hframe ih =>
    intro γ hval h' hQR
    obtain ⟨hq, hr, rfl, hdisj, hQ, hR⟩ := hQR
    obtain ⟨h, hP, hstep⟩ := ih γ hval hq hQ
    rcases frame_addition hstep hr hdisj with ⟨hstepF, hdisj'⟩ | ⟨l, rfl, hmem⟩
    · exact ⟨h ∪ hr, ⟨h, hr, rfl, hdisj', hP, hR⟩, hstepF⟩
    · exact (hframe.not_mem_dom hr hR hmem).elim
  | disj _ _ ih₁ ih₂ =>
    intro γ hval h' hQ
    rcases hQ with hQ₁ | hQ₂
    · obtain ⟨h, hP, hstep⟩ := ih₁ γ hval h' hQ₁
      exact ⟨h, Or.inl hP, hstep⟩
    · obtain ⟨h, hP, hstep⟩ := ih₂ γ hval h' hQ₂
      exact ⟨h, Or.inr hP, hstep⟩
  | cons hsub hPimp hQimp _ ih =>
    intro γ hval h' hQ
    obtain ⟨h, hP', hstep⟩ := ih γ (spec_ctx_inclusion hval hsub) h' (hQimp h' hQ)
    exact ⟨h, hPimp h hP', hstep⟩
  | exists' X _ ih =>
    intro γ hval h' hQ
    obtain ⟨x, hQ'⟩ := hQ
    obtain ⟨h, hP, hstep⟩ := ih γ hval h' hQ'
    exact ⟨h, ⟨x, hP⟩, hstep⟩
  | call hspec =>
    intro γ hval h' hQ
    obtain ⟨xs, e, hsome, hux⟩ := hval _ _ _ _ _ hspec
    obtain ⟨h, hP, hstep⟩ := hux h' hQ
    exact ⟨h, hP, .call hsome hstep⟩

/-- Soundness of specification contexts (`spec_ctx_soundness`). -/
theorem spec_ctx_soundness {γ : ImplCtx} {Γ : SpecCtx} (hctx : γ ≺ₛ Γ) :
    ValidSpecCtx γ Γ := by
  induction hctx with
  | empty => intro f vs P Q ε hin; simp at hin
  | @update Γ' _ P Q ε f xs e vs _ hf hrule heq ih =>
    subst heq
    intro f' vs' P' Q' ε' hin
    by_cases hff : f = f'
    · subst hff
      rw [SpecCtx.update_apply] at hin
      rcases List.mem_cons.mp hin with heq | hin'
      · simp only [FunSpec.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
        exact ⟨_, _, hf, spec_soundness hrule γ ih⟩
      · exact ih f vs' P' Q' ε' hin'
    · rw [SpecCtx.update_apply_ne _ _ hff] at hin
      exact ih f' vs' P' Q' ε' hin

/-- RISL instantiated as a sound UX logic for the refutation algorithm
(`risl`). -/
def risl : Logic where
  DerivableSpec γ e P Q ε := ∃ Γ, (γ ≺ₛ Γ) ∧ (Γ ⊢ ⌈P⌉ e ⌈ε, Q⌉)
  ux_frame_soundness := by
    rintro γ e P Q ε ⟨Γ, hctx, hspec⟩
    exact spec_soundness hspec γ (spec_ctx_soundness hctx)

end RUXt
