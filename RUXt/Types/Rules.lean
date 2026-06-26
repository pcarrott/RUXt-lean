/-
Port of `theories/types/rules.v`: rules of the type system, OX soundness.
-/
import RUXt.Lang.Semantics
import RUXt.Lang.Assertion
import RUXt.Types.Lib.Int
import RUXt.Types.Lib.Bool
import RUXt.Types.Lib.Unit
import RUXt.Types.Lib.Own

namespace RUXt

open scoped RUXt.PMap

/-! ### Over-approximate specifications: typing rules -/

/-- The typing rules (`wf_judg`, `Δ ∣ 𝕋 ⊢ e ⊣ λ𝕌`): from the typings `𝕋`,
running `e` returns a value `v` with typings `λ𝕌 v`. -/
inductive WfJudg : TypeCtx → List Typing → Expr → (Val → List Typing) → Prop
  | int {Δ : TypeCtx} {z : ℤ} :
      WfJudg Δ [] (.pure (.int z)) (fun v => [v ⊲ int])
  | bool {Δ : TypeCtx} {b : Bool} :
      WfJudg Δ [] (.pure (.bool b)) (fun v => [v ⊲ bool])
  | unit {Δ : TypeCtx} :
      WfJudg Δ [] (.pure .unit) (fun v => [v ⊲ unit])
  | minus {Δ : TypeCtx} {p : Pure} :
      WfJudg Δ [] (.pure p) (fun v => [v ⊲ int]) →
      WfJudg Δ [] (.pure (.minus p)) (fun v => [v ⊲ int])
  | not {Δ : TypeCtx} {p : Pure} :
      WfJudg Δ [] (.pure p) (fun v => [v ⊲ bool]) →
      WfJudg Δ [] (.pure (.not p)) (fun v => [v ⊲ bool])
  | add {Δ : TypeCtx} {p₁ p₂ : Pure} :
      WfJudg Δ [] (.pure p₁) (fun v => [v ⊲ int]) →
      WfJudg Δ [] (.pure p₂) (fun v => [v ⊲ int]) →
      WfJudg Δ [] (.pure (.add p₁ p₂)) (fun v => [v ⊲ int])
  | le {Δ : TypeCtx} {p₁ p₂ : Pure} :
      WfJudg Δ [] (.pure p₁) (fun v => [v ⊲ int]) →
      WfJudg Δ [] (.pure p₂) (fun v => [v ⊲ int]) →
      WfJudg Δ [] (.pure (.le p₁ p₂)) (fun v => [v ⊲ bool])
  | assume {Δ : TypeCtx} {b : Bool} :
      WfJudg Δ [] (.assume (.bool b)) (fun _ => [])
  | letIn {Δ : TypeCtx} {x : Binder} {e₁ e₂ : Expr} {𝕋 : List Typing}
      {𝕌f 𝕍f : Val → List Typing} :
      WfJudg Δ 𝕋 e₁ 𝕍f → (∀ v', WfJudg Δ (𝕍f v') (e₂.subst x v') 𝕌f) →
      WfJudg Δ 𝕋 (.letIn x e₁ e₂) 𝕌f
  | choice {Δ : TypeCtx} {e₁ e₂ : Expr} {𝕋 𝕌 : List Typing} :
      WfJudg Δ 𝕋 e₁ (fun _ => 𝕌) → WfJudg Δ 𝕋 e₂ (fun _ => 𝕌) →
      WfJudg Δ 𝕋 (.choice e₁ e₂) (fun _ => 𝕌)
  | val {Δ : TypeCtx} {v' : Val} {τ : Ty} :
      WfJudg Δ [v' ⊲ τ] (.pure (.val v')) (fun v => [v ⊲ τ])
  | alloc {Δ : TypeCtx} :
      WfJudg Δ [] (.alloc (.int 1)) (fun vl => [vl ⊲ empty])
  | free {Δ : TypeCtx} {vl : Val} {τ : Option Ty} :
      WfJudg Δ [vl ⊲ own τ] (.free (.val vl)) (fun _ => [])
  | store {Δ : TypeCtx} {v vl : Val} {τ₁ : Option Ty} {τ₂ : Ty} :
      WfJudg Δ [vl ⊲ own τ₁, v ⊲ τ₂] (.store (.val vl) (.val v)) (fun _ => [vl ⊲ box τ₂])
  | load {Δ : TypeCtx} {vl : Val} {τ : Ty} :
      WfJudg Δ [vl ⊲ box τ] (.load (.val vl)) (fun v => [v ⊲ τ, vl ⊲ empty])
  | frame {Δ : TypeCtx} {e : Expr} {𝕋 𝕌 𝕍 : List Typing} :
      WfJudg Δ 𝕋 e (fun _ => 𝕌) →
      WfJudg Δ (𝕋 ++ 𝕍) e (fun _ => 𝕌 ++ 𝕍)
  | cons {Δ : TypeCtx} {e : Expr} {𝕋 𝕋' : List Typing} {𝕌f 𝕌f' : Val → List Typing} :
      𝕋'.Subperm 𝕋 → (∀ v, (𝕌f v).Subperm (𝕌f' v)) → WfJudg Δ 𝕋' e 𝕌f' →
      WfJudg Δ 𝕋 e 𝕌f
  | call {Δ : TypeCtx} {f : String} {ts : List Term} {τs : List Ty} {τ : Ty}
      {vs : List Val} :
      Δ f = some ⟨τs, τ⟩ → ts = Term.ofVals vs →
      WfJudg Δ (vs [⊲] boxes τs) (.call f ts) (fun v => [v ⊲ box τ])

/-! ### OX semantics -/

/-- `ox_triple`: over-approximate triples for a given evaluation relation. -/
def OXTriple (eval : ImplCtx → Heap → Expr → Heap → Exit → Prop)
    (γ : ImplCtx) (e : Expr) (P : Asrt) (Qf : Val → Asrt) : Prop :=
  ∀ h, hprop h P → ∀ h' ε, eval γ h e h' ε → ∃ v, ε = .ok v ∧ hprop h' (Qf v)

/-- `ox_frame_triple`. -/
def OXFrameTriple (γ : ImplCtx) (e : Expr) (P : Asrt) (Qf : Val → Asrt) : Prop :=
  OXTriple FrameStep γ e P Qf

/-- `ox_full_triple`. -/
def OXFullTriple (γ : ImplCtx) (e : Expr) (P : Asrt) (Qf : Val → Asrt) : Prop :=
  OXTriple BigStep γ e P Qf

/-- `ox_triple_preservation`. -/
theorem ox_triple_preservation {γ : ImplCtx} {e : Expr} {P : Asrt} {Qf : Val → Asrt}
    (hox : OXFullTriple γ e P Qf) : OXFrameTriple γ e P Qf := by
  intro h hh h' ε hstep
  obtain ⟨v, hv⟩ := hox h hh h' (Exit.toFull ε) (semantics_preservation hstep)
  cases ε <;> tauto

/-! ### Semantics of typing judgements -/

/-- `valid_fun_type`. -/
def ValidFunType (γ : ImplCtx) (f : String) (vs : List Val) (τs : List Ty) (τ : Ty) :
    Prop :=
  ∃ xs e, γ f = some ⟨xs, e⟩ ∧
    OXFrameTriple γ (e.substs xs (Term.ofVals vs))
      ([∗ₜ vs [⊲] boxes τs]) (fun v => [∗ₜ [v ⊲ box τ]])

/-- `valid_type_ctx`. -/
def ValidTypeCtx (γ : ImplCtx) (Δ : TypeCtx) : Prop :=
  ∀ f τs τ, Δ f = some ⟨τs, τ⟩ → ∀ vs, ValidFunType γ f vs τs τ

/-- `valid_judg`. -/
def ValidJudg (Δ : TypeCtx) (e : Expr) (𝕋 : List Typing) (𝕌f : Val → List Typing) :
    Prop :=
  ∀ γ, ValidTypeCtx γ Δ → OXFrameTriple γ e ([∗ₜ 𝕋]) (fun v => [∗ₜ 𝕌f v])

/-! ### Per-rule over-approximate triples

Each typing rule of `WfJudg` corresponds to an over-approximate
(`OXFrameTriple`) building block; `judg_soundness` is then a short induction
that applies these. -/

/-- Affine weakening along a sub-permutation: a heap satisfying the affine
ownership of `𝕋` also satisfies the affine ownership of any sub-permutation
`𝕋'` of `𝕋`. -/
theorem iterOwnTypes_subperm_weaken {𝕋 𝕋' : List Typing} (hsub : 𝕋'.Subperm 𝕋)
    {h : Heap} (hh : hprop h ([∗ₜ 𝕋])) : hprop h ([∗ₜ 𝕋']) := by
  rcases hh with ⟨ ha, hb, hab, h₁, h₂ ⟩;
  obtain ⟨ ha', hb', hab', h₁', h₂' ⟩ := hIter_subperm ownType hsub h₂.1;
  refine' ⟨ ha', hb' ∪ hb, _, _, _, _ ⟩ <;> simp_all +decide [ PMap.union_assoc ]

/-- Splitting the affine ownership of an appended list of typings. -/
theorem iterOwnTypes_append_split {𝕋 𝕍 : List Typing} {h : Heap}
    (hh : hprop h ([∗ₜ 𝕋 ++ 𝕍])) :
    ∃ h₁ h₂, h = h₁ ∪ h₂ ∧ h₁ ##ₘ h₂ ∧ hprop h₁ ([∗ₜ 𝕋]) ∧ hprop h₂ ([∗ₜ 𝕍]) := by
  have h_split : hprop h (Asrt.iter 𝕋 ownType ∗ Asrt.iter 𝕍 ownType ∗ .true) → ∃ h₁ h₂ h₃, h = h₁ ∪ h₂ ∪ h₃ ∧ h₁ ##ₘ h₂ ∧ h₁ ##ₘ h₃ ∧ h₂ ##ₘ h₃ ∧ hprop h₁ (Asrt.iter 𝕋 ownType) ∧ hprop h₂ (Asrt.iter 𝕍 ownType) ∧ hprop h₃ .true := by
    intro hh;
    obtain ⟨ h₁, h₂, hh₁, hh₂, hh₃ ⟩ := hStar.mp hh;
    obtain ⟨ h₃, h₄, hh₄, hh₅, hh₆ ⟩ := hStar.mp hh₃.2; use h₁, h₃, h₄; simp_all +decide [ PMap.union_assoc ] ;
  obtain ⟨h₁, h₂, h₃, hh_eq, hh₁₂, hh₁₃, hh₂₃, hh₁, hh₂, hh₃⟩ := h_split (by
  obtain ⟨h₁, h₂, hh₁, hh₂, hh⟩ := hh;
  grind +suggestions);
  refine' ⟨ h₁, h₂ ∪ h₃, _, _, _, _ ⟩;
  · rw [ hh_eq, PMap.union_assoc ];
  · grind +qlia;
  · grind +suggestions;
  · exact ⟨ h₂, h₃, rfl, hh₂₃, hh₂, hh₃ ⟩

/-- Combining the affine ownership of two disjoint heaps. -/
theorem iterOwnTypes_append_combine {𝕌 𝕍 : List Typing} {h₁ h₂ : Heap}
    (hdisj : h₁ ##ₘ h₂) (h₁h : hprop h₁ ([∗ₜ 𝕌])) (h₂h : hprop h₂ ([∗ₜ 𝕍])) :
    hprop (h₁ ∪ h₂) ([∗ₜ 𝕌 ++ 𝕍]) := by
  obtain ⟨a₁, t₁, ha₁, ht₁, h₁h⟩ : ∃ a₁ t₁, h₁ = a₁ ∪ t₁ ∧ a₁ ##ₘ t₁ ∧ hprop a₁ (Asrt.iter 𝕌 ownType) ∧ hprop t₁ .true := h₁h
  obtain ⟨a₂, t₂, ha₂, ht₂, h₂h⟩ : ∃ a₂ t₂, h₂ = a₂ ∪ t₂ ∧ a₂ ##ₘ t₂ ∧ hprop a₂ (Asrt.iter 𝕍 ownType) ∧ hprop t₂ .true := h₂h
  have h_disj : a₁ ##ₘ a₂ ∧ a₁ ##ₘ t₂ ∧ t₁ ##ₘ a₂ ∧ t₁ ##ₘ t₂ := by
    grind +suggestions;
  have h_union : h₁ ∪ h₂ = (a₁ ∪ a₂) ∪ (t₁ ∪ t₂) := by
    simp +decide [ PMap.union_assoc ];
    grind +suggestions;
  simp_all +decide;
  exact ⟨ a₁ ∪ a₂, t₁ ∪ t₂, rfl, by
    grind +suggestions, by
    rw [ hIter_app ];
    exact ⟨ a₁, a₂, rfl, h_disj.1, h₁h, h₂h ⟩, trivial ⟩

/-- A heap satisfying a single type's ownership (plus an arbitrary disjoint
remainder) satisfies the affine ownership of the singleton typing list. -/
theorem iterOwnTypes_singleton_intro {x : Typing} {hx hr : Heap}
    (hdisj : hx ##ₘ hr) (hx_own : hprop hx (ownType x)) :
    hprop (hx ∪ hr) ([∗ₜ [x]]) := by
  convert hStar.mpr _;
  aesop

/-- Introduction for the ownership of `box τ`: a cell pointing to `w` together
with `τ`-ownership of `w`. -/
theorem box_own_intro {l : Loc} {w : Val} {τ : Ty} {hc hd : Heap}
    (hdisj : hc ##ₘ hd) (hc_pt : hprop hc (l ↦ w)) (hd_own : hprop hd (τ.own [w])) :
    hprop (hc ∪ hd) ((box τ).own [.loc l]) := by
  constructor;
  exact ⟨ hc, hd, rfl, hdisj, hc_pt, hd_own ⟩

/-- Introduction for the ownership of `empty` from an initialised cell. -/
theorem empty_own_intro {l : Loc} {w : Val} {hc : Heap}
    (hc_pt : hprop hc (l ↦ w)) : hprop hc (empty.own [.loc l]) := by
  exact Or.inr ⟨ w, hc_pt ⟩

/-- Updating one cell of a singleton-plus-rest heap. -/
theorem hupdate_singleton_union {b : Block} {bv₀ bv : BlockValue} {hkeep : Heap} :
    hupdate (PMap.singleton b bv₀ ∪ hkeep) b bv = PMap.singleton b bv ∪ hkeep := by
  ext b';
  by_cases h : b' = b <;> simp_all +decide [ hupdate_apply, PMap.singleton_apply, PMap.union_apply ]

/-- Extraction of the witnesses hidden in the affine `box` precondition. -/
theorem box_affine_extract {h : Heap} {vl : Val} {τ : Ty}
    (hP : hprop h ([∗ₜ [vl ⊲ box τ]])) :
    ∃ l w hd hrest, vl = .loc l ∧ l.2 = 0 ∧
      h = (PMap.singleton l.1 (.block 1 (PMap.singleton l.2 (.val w))) ∪ hd) ∪ hrest ∧
      PMap.singleton l.1 (.block 1 (PMap.singleton l.2 (.val w))) ##ₘ hd ∧
      (PMap.singleton l.1 (.block 1 (PMap.singleton l.2 (.val w))) ∪ hd) ##ₘ hrest ∧
      hprop (PMap.singleton l.1 (.block 1 (PMap.singleton l.2 (.val w)))) (l ↦ w) ∧
      hprop hd (τ.own [w]) := by
  contrapose! hP; simp +decide at *;
  intro h_contra; rcases h_contra with ⟨ h₁, h₂, h₃, h₄, h₅ ⟩ ; simp_all +decide [ Asrt.iter ] ;
  rcases vl with ( _ | _ | _ | _ | _ ) <;> simp_all +decide [ Asrt.iterL ];
  · cases h₅;
    contradiction;
  · cases h₅;
    contradiction;
  · rcases h₅ with ⟨ w, hw₁, hw₂ ⟩ ; simp_all +decide;
    rcases hw₂ with ⟨ h₂, rfl, h₄, ⟨ rfl, h₅ ⟩, h₆ ⟩ ; simp_all +decide;
    grind;
  · cases h₅;
    contradiction

/-- Extraction of the witnesses hidden in the affine `own τ₁`/`τ₂` store
precondition. -/
theorem own_store_affine_extract {h : Heap} {vl v : Val} {τ₁ : Option Ty} {τ₂ : Ty}
    (hP : hprop h ([∗ₜ [vl ⊲ own τ₁, v ⊲ τ₂]])) :
    ∃ l hv hd hjunk, vl = .loc l ∧ l.2 = 0 ∧
      h = (PMap.singleton l.1 (.block 1 (PMap.singleton l.2 hv)) ∪ hd) ∪ hjunk ∧
      PMap.singleton l.1 (.block 1 (PMap.singleton l.2 hv)) ##ₘ hd ∧
      (PMap.singleton l.1 (.block 1 (PMap.singleton l.2 hv)) ∪ hd) ##ₘ hjunk ∧
      hprop hd (τ₂.own [v]) := by
  rcases vl with ( _ | _ | _ );
  · obtain ⟨ h₁, h₂, h₃, h₄, h₅, h₆ ⟩ := hP;
    obtain ⟨ h₇, h₈, h₉, h₁₀, h₁₁ ⟩ := h₅;
    cases h₁₁.1;
    contradiction;
  · obtain ⟨ ha, hR, hR_true, hR_eq ⟩ := hStar.mp hP;
    obtain ⟨ ha', hR', hR'_true, hR'_eq ⟩ := hStar.mp hR_eq.2.1;
    cases hR'_eq.2.1 ; tauto;
  · rename_i l;
    obtain ⟨ha, hR, h_eq, h_disj, h_own⟩ : ∃ ha hR, h = ha ∪ hR ∧ ha ##ₘ hR ∧ hprop ha ((own τ₁).own [.loc l]) ∧ hprop hR ((τ₂.own [v] ∗ .emp) ∗ .true) := by
      rw [ show [∗ₜ [Val.loc l ⊲ own τ₁, v ⊲ τ₂]] = ((own τ₁).own [Val.loc l] ∗ (τ₂.own [v] ∗ .emp)) ∗ .true from ?_ ] at hP;
      · simp +decide at hP ⊢;
        obtain ⟨ h₂, h₁, h₂_1, rfl, ⟨ h₁h₂, h₂_1h₂ ⟩, h₁h₂_1, h₁h₂_1', h₂_1h₂' ⟩ := hP; use h₁, h₂_1, h₂; simp_all +decide [ PMap.union_assoc ] ;
      · rfl;
    obtain ⟨hv, hv_eq⟩ : ∃ hv, ha l.1 = some (.block 1 (PMap.singleton l.2 hv)) ∧ l.2 = 0 := by
      have := own_loc h_own.1; aesop;
    obtain ⟨hd, htrue, hR_eq, h_disj', h_own'⟩ : ∃ hd htrue, hR = hd ∪ htrue ∧ hd ##ₘ htrue ∧ hprop hd (τ₂.own [v]) := by
      simp +zetaDelta at *;
      exact h_own.2;
    obtain ⟨ha', ha'_eq, ha'_disj⟩ : ∃ ha', ha = PMap.singleton l.1 (.block 1 (PMap.singleton l.2 hv)) ∪ ha' ∧ PMap.singleton l.1 (.block 1 (PMap.singleton l.2 hv)) ##ₘ ha' ∧ l.1 ∉ ha'.dom := by
      refine' ⟨ fun b => if b = l.1 then none else ha b, _, _, _ ⟩ <;> simp +decide [ PMap.singleton ];
      unfold PMap.insert; aesop;
    refine' ⟨ l, hv, hd, ha' ∪ htrue, rfl, hv_eq.2, _, _, _, _ ⟩ <;> simp_all +decide [ PMap.union_assoc ];
    · grind +suggestions;
    · exact h_disj.1.2.symm;
  · rcases hP with ⟨ h₁, h₂, h₃ ⟩;
    rcases h₃.2.2.1 with ⟨ h₄, h₅, h₆ ⟩;
    rcases h₆.2.2.1 with ⟨ h₇, h₈, h₉ ⟩

/-- OX triple for the `int` rule. -/
theorem ox_int {γ : ImplCtx} {z : ℤ} :
    OXFrameTriple γ (.pure (.int z)) ([∗ₜ []]) (fun v => [∗ₜ [v ⊲ int]]) := by
  intro h hP;
  rintro h' ε ⟨ _v, _hstep ⟩;
  simp_all +decide [ Asrt.iter, Asrt.iterL, iterOwnTypes ];
  use ∅, h;
  exact ⟨ rfl, by tauto ⟩

/-- OX triple for the `bool` rule. -/
theorem ox_bool {γ : ImplCtx} {b : Bool} :
    OXFrameTriple γ (.pure (.bool b)) ([∗ₜ []]) (fun v => [∗ₜ [v ⊲ bool]]) := by
  intro h hP h' ε hstep;
  cases hstep;
  cases b <;> cases ‹_› <;> simp_all +decide;
  · cases hP;
    rename_i h₁ h₂;
    obtain ⟨ h₂, rfl, h₃, h₄, h₅ ⟩ := h₂;
    use ∅, h₁ ∪ h₂;
    simp +decide [ hprop ];
    exact ⟨ rfl, by tauto ⟩;
  · constructor;
    swap;
    exact ∅;
    simp +decide [ hprop ];
    trivial

/-- OX triple for the `unit` rule. -/
theorem ox_unit {γ : ImplCtx} :
    OXFrameTriple γ (.pure .unit) ([∗ₜ []]) (fun v => [∗ₜ [v ⊲ unit]]) := by
  intro h hP h' ε hstep
  cases hstep;
  cases ‹Pure.unit.eval = some _›;
  simp +decide at hP ⊢;
  use ∅, h;
  simp +decide [ hprop ];
  trivial

/-- OX triple for the `minus` rule. The typing premise on `p` is not needed:
the operational semantics already forces the operand to be an integer. -/
theorem ox_minus {γ : ImplCtx} {p : Pure} :
    OXFrameTriple γ (.pure (.minus p)) ([∗ₜ []]) (fun v => [∗ₜ [v ⊲ int]]) := by
  intro h₀ h₁ h' ε h₂;
  cases h₂;
  cases h : p.eval <;> simp_all +decide [ Pure.eval ];
  cases ‹Val› <;> cases ‹UnOp.minus.eval _ = _›;
  use ∅, h₀;
  simp +decide [ ownType ];
  exact ⟨ rfl, trivial ⟩

/-- OX triple for the `not` rule. -/
theorem ox_not {γ : ImplCtx} {p : Pure}
    (h : OXFrameTriple γ (.pure p) ([∗ₜ []]) (fun v => [∗ₜ [v ⊲ bool]])) :
    OXFrameTriple γ (.pure (.not p)) ([∗ₜ []]) (fun v => [∗ₜ [v ⊲ bool]]) := by
  intro hP; simp_all +decide [ OXFrameTriple ] ;
  intro hP' h' ε hstep; cases hstep; simp_all +decide;
  rename_i v hv;
  obtain ⟨w, hw⟩ : ∃ w, p.eval = some w ∧ UnOp.eval .not w = v := by
    cases h : p.eval <;> simp_all +decide [ Pure.eval ];
  rcases w with ( _ | _ | _ | _ ) <;> simp_all +decide [ UnOp.eval ];
  have := h hP hP' hP ( Exit.ok ( Val.bool ‹_› ) ) ( FrameStep.pure hw.1 ) ; aesop;

/-- OX triple for the `add` rule. Only the typing premise on `p₁` is needed;
the operational semantics forces both operands to be integers. -/
theorem ox_add {γ : ImplCtx} {p₁ p₂ : Pure}
    (h₁ : OXFrameTriple γ (.pure p₁) ([∗ₜ []]) (fun v => [∗ₜ [v ⊲ int]])) :
    OXFrameTriple γ (.pure (.add p₁ p₂)) ([∗ₜ []]) (fun v => [∗ₜ [v ⊲ int]]) := by
  intro h hP h' ε hstep;
  rcases hstep with ⟨ ⟩;
  rcases h : p₁.eval with ( _ | v₁ ) <;> rcases h' : p₂.eval with ( _ | v₂ ) <;> simp_all +decide [ Pure.eval ];
  rcases v₁ with ( _ | _ | _ | v₁ ) <;> rcases v₂ with ( _ | _ | _ | v₂ ) <;> norm_cast at *;
  cases ‹BinOp.add.eval _ _ = _›;
  have := h₁ _ hP;
  specialize this _ _ ( FrameStep.pure h ) ; aesop

/-- OX triple for the `le` rule. No typing premises are needed: the result of
`le` is always a boolean. -/
theorem ox_le {γ : ImplCtx} {p₁ p₂ : Pure} :
    OXFrameTriple γ (.pure (.le p₁ p₂)) ([∗ₜ []]) (fun v => [∗ₜ [v ⊲ bool]]) := by
  intro h hP h' ε hstep;
  cases hstep;
  rename_i v hv;
  cases v <;> simp_all +decide;
  · cases hv' : p₁.eval <;> cases hv'' : p₂.eval <;> simp_all +decide [ Pure.eval ];
    unfold BinOp.eval at hv; aesop;
  · constructor;
    swap;
    exact ∅;
    simp +decide;
    exact ⟨ rfl, by tauto ⟩;
  · cases hv' : p₁.eval <;> cases hv'' : p₂.eval <;> simp_all +decide [ Pure.eval ];
    cases ‹Val› <;> cases ‹Val› <;> cases hv;
  · cases h : p₁.eval <;> cases h' : p₂.eval <;> simp_all +decide [ Pure.eval ];
    cases ‹Val› <;> cases ‹Val› <;> cases hv

/-- OX triple for the `assume` rule. -/
theorem ox_assume {γ : ImplCtx} {b : Bool} :
    OXFrameTriple γ (.assume (.bool b)) ([∗ₜ []]) (fun _ => [∗ₜ []]) := by
  intro h;
  grind +splitIndPred

/-- OX triple for the `val` rule. -/
theorem ox_val {γ : ImplCtx} {v' : Val} {τ : Ty} :
    OXFrameTriple γ (.pure (.val v')) ([∗ₜ [v' ⊲ τ]]) (fun v => [∗ₜ [v ⊲ τ]]) := by
  intros h hP h' ε hstep; cases hstep;
  cases ‹ ( Pure.val v' ).eval = some _› ; tauto

/-- OX triple for the `letIn` rule. -/
theorem ox_letIn {γ : ImplCtx} {x : Binder} {e₁ e₂ : Expr} {𝕋 : List Typing}
    {𝕍f 𝕌f : Val → List Typing}
    (h₁ : OXFrameTriple γ e₁ ([∗ₜ 𝕋]) (fun v => [∗ₜ 𝕍f v]))
    (h₂ : ∀ v', OXFrameTriple γ (e₂.subst x v') ([∗ₜ 𝕍f v']) (fun v => [∗ₜ 𝕌f v])) :
    OXFrameTriple γ (.letIn x e₁ e₂) ([∗ₜ 𝕋]) (fun v => [∗ₜ 𝕌f v]) := by
  intro h hP;
  rintro h' ε ⟨ hstep₁, hstep₂ ⟩;
  · rename_i h'' v hv₁ hv₂;
    obtain ⟨ v', hv'₁, hv'₂ ⟩ := h₁ h hP h'' ( Exit.ok v ) hv₁; specialize h₂ v'; aesop;
  · have := h₁ h hP h' ε ‹_›; tauto;

/-- OX triple for the `choice` rule. -/
theorem ox_choice {γ : ImplCtx} {e₁ e₂ : Expr} {𝕋 𝕌 : List Typing}
    (h₁ : OXFrameTriple γ e₁ ([∗ₜ 𝕋]) (fun _ => [∗ₜ 𝕌]))
    (h₂ : OXFrameTriple γ e₂ ([∗ₜ 𝕋]) (fun _ => [∗ₜ 𝕌])) :
    OXFrameTriple γ (.choice e₁ e₂) ([∗ₜ 𝕋]) (fun _ => [∗ₜ 𝕌]) := by
  intro h hP h' ε hstep;
  cases hstep;
  rename_i eᵢ he₁₂ hstep;
  rcases he₁₂ with ( rfl | rfl ) <;> [ exact h₁ h hP h' ε hstep; exact h₂ h hP h' ε hstep ]

/-- OX triple for the `alloc` rule. -/
theorem ox_alloc {γ : ImplCtx} :
    OXFrameTriple γ (.alloc (.int 1)) ([∗ₜ []]) (fun vl => [∗ₜ [vl ⊲ empty]]) := by
  intro h hP h' ε hstep;
  obtain ⟨l, hl⟩ : ∃ l : Loc, ε = .ok (.loc l) ∧ h' = hstore h l.1 1 (balloc 1) ∧ l.2 = 0 ∧ l.1 ∉ h.dom := by
    cases hstep;
    cases ‹Term.eval ( Term.int 1 ) = some ( Val.int _ ) ›;
    grind;
  simp_all +decide;
  use PMap.singleton l.1 (.block 1 (PMap.singleton l.2 .poison)), h;
  refine' ⟨ _, _, _ ⟩;
  · unfold hstore balloc breplicate; aesop;
  · cases h : h l.1 <;> aesop;
  · unfold ownType;
    unfold empty; simp +decide;
    unfold own; simp +decide;
    exact Or.inl hl.2.2.1

/-- OX triple for the `free` rule. -/
theorem ox_free {γ : ImplCtx} {vl : Val} {τ : Option Ty} :
    OXFrameTriple γ (.free (.val vl)) ([∗ₜ [vl ⊲ own τ]]) (fun _ => [∗ₜ []]) := by
  intro h hP
  obtain ⟨ha, hha⟩ : ∃ ha, ha ⊆ h ∧ hprop ha ((own τ).own [vl]) := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hP;
    use h₁;
    exact ⟨ fun l => by aesop, by simpa [ Asrt.iterL ] using h₅ ⟩;
  obtain ⟨l, hl⟩ : ∃ l : Loc, vl = .loc l := by
    rcases vl with ( _ | _ | _ | _ | vl ) <;> simp_all +decide;
    · cases hha.2 ; aesop;
    · cases hha.2 ; aesop;
    · cases hha.2;
      contradiction;
  intro h' ε hstep;
  obtain ⟨l2, hl2⟩ : l.2 = 0 ∧ ∃ hv, h l.1 = some (.block 1 (PMap.singleton l.2 hv)) := by
    have := own_loc ( by aesop : hprop ha ( ( own τ ).own [ .loc l ] ) ) ; aesop;
  obtain ⟨hv, hhv⟩ := hl2;
  rcases hstep with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | hstep ) <;> simp_all +decide;
  exact ⟨ ∅, by simp +decide [ hprop ] ⟩

/-- OX triple for the `store` rule. -/
theorem ox_store {γ : ImplCtx} {v vl : Val} {τ₁ : Option Ty} {τ₂ : Ty} :
    OXFrameTriple γ (.store (.val vl) (.val v)) ([∗ₜ [vl ⊲ own τ₁, v ⊲ τ₂]])
      (fun _ => [∗ₜ [vl ⊲ box τ₂]]) := by
  intro h₁ h₂ h₃ h₄ h₅;
  cases h₅;
  · rename_i l sz bh v hl₁ hl₂ hl₃ hl₄ hl₅;
    rcases h : own_store_affine_extract h₂ with ⟨ l', hv', hd', hjunk', rfl, hl₂', rfl, hdisj₁, hdisj₂, hprop₁ ⟩ ; simp_all +decide [ PMap.union_assoc ];
    subst_vars;
    convert iterOwnTypes_singleton_intro _ _ using 1;
    rotate_left;
    exact PMap.singleton l'.1 ( BlockValue.block 1 ( PMap.singleton l'.2 ( HeapValue.val v ) ) ) ∪ hd';
    exact hjunk';
    · grind;
    · convert box_own_intro _ _ _ using 1;
      exact v;
      · grind;
      · exact ⟨ rfl, hl₂' ⟩;
      · exact hprop₁;
    · convert hupdate_singleton_union using 1;
      rw [ ← PMap.union_assoc ] ; congr ; aesop;
      · exact hl₂.1;
      · unfold bupdate; aesop;
  · obtain ⟨ l, hv, hd, hjunk, rfl, hl2, hsum, hdisj, hdisj', hd_own ⟩ := own_store_affine_extract h₂;
    cases hv <;> simp_all +decide;
  · obtain ⟨ l, hv, hd, hjunk, rfl, hl2, hsum, hdisj, hdisj', hd_own ⟩ := own_store_affine_extract h₂;
    simp_all +decide [ Term.eval ];
  · have := own_store_affine_extract h₂; aesop;

/-- OX triple for the `load` rule. -/
theorem ox_load {γ : ImplCtx} {vl : Val} {τ : Ty} :
    OXFrameTriple γ (.load (.val vl)) ([∗ₜ [vl ⊲ box τ]])
      (fun v => [∗ₜ [v ⊲ τ, vl ⊲ empty]]) := by
  intro h hP;
  obtain ⟨l, w, hd, hrest, hvl, hl2, h_eq, hdisj, hrest_disj, hhc, hd_own⟩ := box_affine_extract hP;
  intro h' ε hstep
  obtain ⟨v, hv⟩ : ∃ v, ε = .ok v ∧ h' = h := by
    rcases hstep with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | hstep ) <;> simp_all +decide;
    · rename_i k hk₁ hk₂ hk₃;
      rcases hk₂ with ⟨ rfl, rfl ⟩ ; simp_all +decide [ PMap.singleton ];
    · rename_i k hk₁ hk₂ hk₃;
      rcases hk₂ with ⟨ rfl, rfl ⟩ ; tauto;
  have hτ : hprop hd ([∗ₜ [w ⊲ τ]]) := by
    convert iterOwnTypes_singleton_intro _ _ using 1;
    rotate_left;
    exact hd;
    exact ∅;
    · exact PMap.disjoint_empty_r hd;
    · exact hd_own;
    · exact Eq.symm ( PMap.union_empty _ )
  have hemp : hprop (PMap.singleton l.1 (BlockValue.block 1 (PMap.singleton l.2 (HeapValue.val w))) ∪ hrest) ([∗ₜ [.loc l ⊲ empty]]) := by
    apply iterOwnTypes_singleton_intro;
    · grind +locals;
    · exact empty_own_intro hhc
  have hdisj' : hd ##ₘ (PMap.singleton l.1 (BlockValue.block 1 (PMap.singleton l.2 (HeapValue.val w))) ∪ hrest) := by
    grind
  have h_final : hprop (hd ∪ (PMap.singleton l.1 (BlockValue.block 1 (PMap.singleton l.2 (HeapValue.val w))) ∪ hrest)) ([∗ₜ [w ⊲ τ, .loc l ⊲ empty]]) := by
    exact iterOwnTypes_append_combine hdisj' hτ hemp
  simp_all +decide [ PMap.union_assoc, PMap.union_comm ];
  cases hstep ; aesop

/-- OX triple for the `frame` rule. -/
theorem ox_frame {γ : ImplCtx} {e : Expr} {𝕋 𝕌 𝕍 : List Typing}
    (h : OXFrameTriple γ e ([∗ₜ 𝕋]) (fun _ => [∗ₜ 𝕌])) :
    OXFrameTriple γ e ([∗ₜ 𝕋 ++ 𝕍]) (fun _ => [∗ₜ 𝕌 ++ 𝕍]) := by
  intro ht hP h' ε hstep
  obtain ⟨h𝕋, h𝕍, rfl, hdisj, hT, hV⟩ := iterOwnTypes_append_split hP
  obtain ⟨hs', hdisj', hcase⟩ := frame_subtraction hstep h𝕋 h𝕍 rfl hdisj
  rcases hcase with ⟨hstep', rfl⟩ | ⟨l, hmiss, -⟩
  · obtain ⟨v, rfl, hpost⟩ := h h𝕋 hT hs' ε hstep'
    exact ⟨v, rfl, iterOwnTypes_append_combine hdisj' hpost hV⟩
  · obtain ⟨v, hv, -⟩ := h h𝕋 hT hs' (.miss l) hmiss
    exact absurd hv (by simp)

/-- OX triple for the `cons` rule. -/
theorem ox_cons {γ : ImplCtx} {e : Expr} {𝕋 𝕋' : List Typing}
    {𝕌f 𝕌f' : Val → List Typing}
    (hsubT : 𝕋'.Subperm 𝕋) (hsubU : ∀ v, (𝕌f v).Subperm (𝕌f' v))
    (h : OXFrameTriple γ e ([∗ₜ 𝕋']) (fun v => [∗ₜ 𝕌f' v])) :
    OXFrameTriple γ e ([∗ₜ 𝕋]) (fun v => [∗ₜ 𝕌f v]) := by
  intro ht hP h' ε hstep
  obtain ⟨v, rfl, hpost⟩ := h ht (iterOwnTypes_subperm_weaken hsubT hP) h' ε hstep
  exact ⟨v, rfl, iterOwnTypes_subperm_weaken (hsubU v) hpost⟩

/-- OX triple for the `call` rule. -/
theorem ox_call {γ : ImplCtx} {Δ : TypeCtx} {f : String} {τs : List Ty} {τ : Ty}
    {vs : List Val} (hΔ : ValidTypeCtx γ Δ) (hf : Δ f = some ⟨τs, τ⟩) :
    OXFrameTriple γ (.call f (Term.ofVals vs)) ([∗ₜ vs [⊲] boxes τs])
      (fun v => [∗ₜ [v ⊲ box τ]]) := by
  obtain ⟨xs, e, hγf, htriple⟩ := hΔ f τs τ hf vs;
  intro h hP h' ε hstep;
  cases hstep;
  cases hγf.symm.trans ‹γ f = some { params := _, body := _ } › ; tauto

/-- Soundness of the typing rules (`judg_soundness`). -/
theorem judg_soundness {Δ : TypeCtx} {𝕋 : List Typing} {e : Expr}
    {𝕌f : Val → List Typing} (hrule : WfJudg Δ 𝕋 e 𝕌f) : ValidJudg Δ e 𝕋 𝕌f := by
  induction hrule with
  | int => intro γ _; exact ox_int
  | bool => intro γ _; exact ox_bool
  | unit => intro γ _; exact ox_unit
  | minus _ _ => intro γ _; exact ox_minus
  | not _ ih => intro γ hΔ; exact ox_not (ih γ hΔ)
  | add _ _ ih₁ _ => intro γ hΔ; exact ox_add (ih₁ γ hΔ)
  | le _ _ _ _ => intro γ _; exact ox_le
  | assume => intro γ _; exact ox_assume
  | letIn _ _ ih₁ ih₂ => intro γ hΔ; exact ox_letIn (ih₁ γ hΔ) (fun v' => ih₂ v' γ hΔ)
  | choice _ _ ih₁ ih₂ => intro γ hΔ; exact ox_choice (ih₁ γ hΔ) (ih₂ γ hΔ)
  | val => intro γ _; exact ox_val
  | alloc => intro γ _; exact ox_alloc
  | free => intro γ _; exact ox_free
  | store => intro γ _; exact ox_store
  | load => intro γ _; exact ox_load
  | frame _ ih => intro γ hΔ; exact ox_frame (ih γ hΔ)
  | cons hsubT hsubU _ ih => intro γ hΔ; exact ox_cons hsubT hsubU (ih γ hΔ)
  | call hf hts => intro γ hΔ; subst hts; exact ox_call hΔ hf

end RUXt
