/-
Port of `theories/lang/semantics.v`: operational semantics, frame preservation.
-/
import RUXt.Lang.Lang

namespace RUXt

open scoped RUXt.PMap

/-! ### Program context -/

/-- Function implementations (`fun_impl`, Rocq notation `{(xs) e}`). -/
structure FunImpl where
  params : List String
  body : Expr

/-- Implementation contexts. -/
abbrev ImplCtx := PMap String FunImpl

/-! ### Heaps -/

/-- Heap values: a value or the uninitialised `poison`. -/
inductive HeapValue
  | val (v : Val)
  | poison
deriving DecidableEq

/-- Block heaps: partial maps from offsets to heap values. -/
abbrev BlockHeap := PMap ℕ HeapValue

/-- Block values: a live block of a given size, or a freed block. -/
inductive BlockValue
  | block (sz : ℕ) (bh : BlockHeap)
  | freed

/-- Heaps: partial maps from blocks to block values. -/
abbrev Heap := PMap Block BlockValue

/-! ### Heap operations -/

/-- `breplicate`. -/
def breplicate (hv : HeapValue) : ℕ → BlockHeap
  | 0 => ∅
  | n + 1 => (breplicate hv n).insert n hv

/-- `balloc`: a freshly allocated block heap of `n` poison cells. -/
abbrev balloc : ℕ → BlockHeap := breplicate .poison

/-- `bupdate`. -/
def bupdate (bh : BlockHeap) (i : ℕ) (v : Val) : BlockHeap :=
  bh.insert i (.val v)

/-- `hupdate`. -/
def hupdate (h : Heap) (b : Block) (bv : BlockValue) : Heap :=
  PMap.insert b bv h

/-- `hstore`. -/
abbrev hstore (h : Heap) (b : Block) (sz : ℕ) (bh : BlockHeap) : Heap :=
  hupdate h b (.block sz bh)

/-- `hfree`. -/
abbrev hfree (h : Heap) (b : Block) : Heap :=
  hupdate h b .freed

@[simp, grind =] theorem hupdate_apply (h : Heap) (b : Block) (bv : BlockValue) (b' : Block) :
    hupdate h b bv b' = if b' = b then some bv else h b' := rfl

/-- `hupdate_disj`. -/
theorem hupdate_disj {h h' : Heap} {b : Block} {bv : BlockValue} :
    hupdate h b bv ##ₘ h' ↔ h ##ₘ h' ∧ b ∉ h'.dom := by
  unfold hupdate
  rw [PMap.disjoint_insert_l]
  simp only [PMap.not_mem_dom]
  exact and_comm

/-- `hupdate_union`. -/
theorem hupdate_union {h h' : Heap} {b : Block} {bv : BlockValue}
    (_ : hupdate h b bv ##ₘ h') :
    hupdate h b bv ∪ h' = hupdate (h ∪ h') b bv :=
  PMap.insert_union_l ..

/-! ### Termination -/

/-- Termination tags (`exit`). -/
inductive Exit
  | ok (v : Val)
  | err
  | miss (l : Loc)
deriving DecidableEq

instance : Countable Exit := by
  have : Function.Injective (fun ε : Exit => match ε with
      | .ok v => Sum.inl (some v)
      | .err => Sum.inl none
      | .miss l => Sum.inr l : Exit → Option Val ⊕ Loc) := by
    intro ε₁ ε₂ h; cases ε₁ <;> cases ε₂ <;> simp_all
  exact this.countable

/-! ### Operational semantics

`BigStep` is the full semantics (`eval_expr`, `γ ⊢ ⟨h | e⟩ ⇓ ⟨h' | ε⟩`),
`FrameStep` the instrumented semantics (`eval_expr_frame`,
`γ ⊢ ⟨h | e⟩ ⇓ᵢ ⟨h' | ε⟩`), which reports misses on locations outside the
current heap fragment. -/

/-- The full big-step semantics (`eval_expr`). -/
inductive BigStep (γ : ImplCtx) : Heap → Expr → Heap → Exit → Prop
  | pure {p : Pure} {h : Heap} {v : Val} :
      p.eval = some v →
      BigStep γ h (.pure p) h (.ok v)
  | assume {h : Heap} :
      BigStep γ h (.assume .true) h (.ok .unit)
  | error {h : Heap} :
      BigStep γ h .error h .err
  | letIn {x : Binder} {e₁ e₂ : Expr} {h h' h'' : Heap} {v : Val} {ε : Exit} :
      BigStep γ h e₁ h'' (.ok v) → BigStep γ h'' (e₂.subst x v) h' ε →
      BigStep γ h (.letIn x e₁ e₂) h' ε
  | letCut {x : Binder} {e₁ e₂ : Expr} {h h' : Heap} {ε : Exit} :
      BigStep γ h e₁ h' ε → (¬ ∃ v, ε = .ok v) →
      BigStep γ h (.letIn x e₁ e₂) h' ε
  | choice {eᵢ e₁ e₂ : Expr} {h h' : Heap} {ε : Exit} :
      BigStep γ h eᵢ h' ε → (eᵢ = e₁ ∨ eᵢ = e₂) →
      BigStep γ h (.choice e₁ e₂) h' ε
  | alloc {t : Term} {h h' : Heap} {l : Loc} {n : ℕ} :
      t.eval = some (.int n) →
      l.1 ∉ h.dom → l.2 = 0 →
      h' = hstore h l.1 n (balloc n) →
      BigStep γ h (.alloc t) h' (.ok (.loc l))
  | free {t : Term} {h h' : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t.eval = some (.loc l) →
      h l.1 = some (.block sz bh) → l.2 = 0 → (∀ i < sz, i ∈ bh.dom) →
      h' = hfree h l.1 →
      BigStep γ h (.free t) h' (.ok .unit)
  | freeErr {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      h l.1 = some .freed →
      BigStep γ h (.free t) h .err
  | freeErrBlock {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      l.2 ≠ 0 →
      BigStep γ h (.free t) h .err
  | freeMiss {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      l.1 ∉ h.dom →
      BigStep γ h (.free t) h .err
  | freeMissBlock {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} {i : ℕ} :
      t.eval = some (.loc l) →
      h l.1 = some (.block sz bh) → i < sz → i ∉ bh.dom →
      BigStep γ h (.free t) h .err
  | store {t₁ t₂ : Term} {h h' : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} {v : Val} :
      t₁.eval = some (.loc l) → t₂.eval = some v →
      h l.1 = some (.block sz bh) → l.2 ∈ bh.dom →
      h' = hstore h l.1 sz (bupdate bh l.2 v) →
      BigStep γ h (.store t₁ t₂) h' (.ok .unit)
  | storeErr {t₁ t₂ : Term} {h : Heap} {l : Loc} :
      t₁.eval = some (.loc l) →
      h l.1 = some .freed →
      BigStep γ h (.store t₁ t₂) h .err
  | storeMiss {t₁ t₂ : Term} {h : Heap} {l : Loc} :
      t₁.eval = some (.loc l) →
      l.1 ∉ h.dom →
      BigStep γ h (.store t₁ t₂) h .err
  | storeMissBlock {t₁ t₂ : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t₁.eval = some (.loc l) →
      h l.1 = some (.block sz bh) → l.2 ∉ bh.dom →
      BigStep γ h (.store t₁ t₂) h .err
  | load {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} {v : Val} :
      t.eval = some (.loc l) →
      h l.1 = some (.block sz bh) → bh l.2 = some (.val v) →
      BigStep γ h (.load t) h (.ok v)
  | loadErr {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      h l.1 = some .freed →
      BigStep γ h (.load t) h .err
  | loadErrBlock {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t.eval = some (.loc l) →
      h l.1 = some (.block sz bh) → bh l.2 = some .poison →
      BigStep γ h (.load t) h .err
  | loadMiss {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      l.1 ∉ h.dom →
      BigStep γ h (.load t) h .err
  | loadMissBlock {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t.eval = some (.loc l) →
      h l.1 = some (.block sz bh) → l.2 ∉ bh.dom →
      BigStep γ h (.load t) h .err
  | call {f : String} {xs : List String} {e : Expr} {ts : List Term} {h h' : Heap} {ε : Exit} :
      γ f = some ⟨xs, e⟩ → BigStep γ h (e.substs xs ts) h' ε →
      BigStep γ h (.call f ts) h' ε

@[inherit_doc] scoped notation:50 γ:51 " ⊢ " "⟨" h " | " e "⟩" " ⇓ " "⟨" h' " | " ε "⟩" =>
  BigStep γ h e h' ε

/-- The instrumented big-step semantics (`eval_expr_frame`). -/
inductive FrameStep (γ : ImplCtx) : Heap → Expr → Heap → Exit → Prop
  | pure {p : Pure} {h : Heap} {v : Val} :
      p.eval = some v →
      FrameStep γ h (.pure p) h (.ok v)
  | assume {h : Heap} :
      FrameStep γ h (.assume .true) h (.ok .unit)
  | error {h : Heap} :
      FrameStep γ h .error h .err
  | letIn {x : Binder} {e₁ e₂ : Expr} {h h' h'' : Heap} {v : Val} {ε : Exit} :
      FrameStep γ h e₁ h'' (.ok v) → FrameStep γ h'' (e₂.subst x v) h' ε →
      FrameStep γ h (.letIn x e₁ e₂) h' ε
  | letCut {x : Binder} {e₁ e₂ : Expr} {h h' : Heap} {ε : Exit} :
      FrameStep γ h e₁ h' ε → (¬ ∃ v, ε = .ok v) →
      FrameStep γ h (.letIn x e₁ e₂) h' ε
  | choice {eᵢ e₁ e₂ : Expr} {h h' : Heap} {ε : Exit} :
      FrameStep γ h eᵢ h' ε → (eᵢ = e₁ ∨ eᵢ = e₂) →
      FrameStep γ h (.choice e₁ e₂) h' ε
  | alloc {t : Term} {h h' : Heap} {l : Loc} {n : ℕ} :
      t.eval = some (.int n) →
      l.1 ∉ h.dom → l.2 = 0 →
      h' = hstore h l.1 n (balloc n) →
      FrameStep γ h (.alloc t) h' (.ok (.loc l))
  | free {t : Term} {h h' : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t.eval = some (.loc l) →
      h l.1 = some (.block sz bh) → l.2 = 0 → (∀ i < sz, i ∈ bh.dom) →
      h' = hfree h l.1 →
      FrameStep γ h (.free t) h' (.ok .unit)
  | freeErr {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      h l.1 = some .freed →
      FrameStep γ h (.free t) h .err
  | freeErrBlock {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      l.2 ≠ 0 →
      FrameStep γ h (.free t) h .err
  | freeMiss {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      l.1 ∉ h.dom →
      FrameStep γ h (.free t) h (.miss l)
  | freeMissBlock {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} {i : ℕ} :
      t.eval = some (.loc l) →
      h l.1 = some (.block sz bh) → i < sz → i ∉ bh.dom →
      FrameStep γ h (.free t) h (.miss (l +ₗ i))
  | store {t₁ t₂ : Term} {h h' : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} {v : Val} :
      t₁.eval = some (.loc l) → t₂.eval = some v →
      h l.1 = some (.block sz bh) → l.2 ∈ bh.dom →
      h' = hstore h l.1 sz (bupdate bh l.2 v) →
      FrameStep γ h (.store t₁ t₂) h' (.ok .unit)
  | storeErr {t₁ t₂ : Term} {h : Heap} {l : Loc} :
      t₁.eval = some (.loc l) →
      h l.1 = some .freed →
      FrameStep γ h (.store t₁ t₂) h .err
  | storeMiss {t₁ t₂ : Term} {h : Heap} {l : Loc} :
      t₁.eval = some (.loc l) →
      l.1 ∉ h.dom →
      FrameStep γ h (.store t₁ t₂) h (.miss l)
  | storeMissBlock {t₁ t₂ : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t₁.eval = some (.loc l) →
      h l.1 = some (.block sz bh) → l.2 ∉ bh.dom →
      FrameStep γ h (.store t₁ t₂) h (.miss l)
  | load {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} {v : Val} :
      t.eval = some (.loc l) →
      h l.1 = some (.block sz bh) → bh l.2 = some (.val v) →
      FrameStep γ h (.load t) h (.ok v)
  | loadErr {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      h l.1 = some .freed →
      FrameStep γ h (.load t) h .err
  | loadErrBlock {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t.eval = some (.loc l) →
      h l.1 = some (.block sz bh) → bh l.2 = some .poison →
      FrameStep γ h (.load t) h .err
  | loadMiss {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      l.1 ∉ h.dom →
      FrameStep γ h (.load t) h (.miss l)
  | loadMissBlock {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t.eval = some (.loc l) →
      h l.1 = some (.block sz bh) → l.2 ∉ bh.dom →
      FrameStep γ h (.load t) h (.miss l)
  | call {f : String} {xs : List String} {e : Expr} {ts : List Term} {h h' : Heap} {ε : Exit} :
      γ f = some ⟨xs, e⟩ → FrameStep γ h (e.substs xs ts) h' ε →
      FrameStep γ h (.call f ts) h' ε

@[inherit_doc] scoped notation:50 γ:51 " ⊢ " "⟨" h " | " e "⟩" " ⇓ᵢ " "⟨" h' " | " ε "⟩" =>
  FrameStep γ h e h' ε

/-! ### Frame properties -/

/-- Under-approximate frame validity — `frame_addition`. -/
theorem frame_addition {γ : ImplCtx} {h e h' ε} (hstep : γ ⊢ ⟨h | e⟩ ⇓ᵢ ⟨h' | ε⟩) :
    ∀ hF, h' ##ₘ hF →
    ((γ ⊢ ⟨h ∪ hF | e⟩ ⇓ᵢ ⟨h' ∪ hF | ε⟩) ∧ h ##ₘ hF) ∨
    (∃ l, ε = .miss l ∧ l.1 ∈ hF.dom) := by
  induction hstep with
  | pure hp => exact fun hF hd => .inl ⟨.pure hp, hd⟩
  | assume => exact fun hF hd => .inl ⟨.assume, hd⟩
  | error => exact fun hF hd => .inl ⟨.error, hd⟩
  | letIn hstep₁ hstep₂ ih₁ ih₂ =>
    intro hF hdisj'
    rcases ih₂ hF hdisj' with ⟨hstep₂F, hdisj''⟩ | hmiss
    · rcases ih₁ hF hdisj'' with ⟨hstep₁F, hdisj⟩ | ⟨l, hl, _⟩
      · exact .inl ⟨.letIn hstep₁F hstep₂F, hdisj⟩
      · exact absurd hl (by simp)
    · exact .inr hmiss
  | letCut hstep hne ih =>
    intro hF hdisj'
    rcases ih hF hdisj' with ⟨hstepF, hdisj⟩ | hmiss
    · exact .inl ⟨.letCut hstepF hne, hdisj⟩
    · exact .inr hmiss
  | choice hstep hor ih =>
    intro hF hdisj'
    rcases ih hF hdisj' with ⟨hstepF, hdisj⟩ | hmiss
    · exact .inl ⟨.choice hstepF hor, hdisj⟩
    · exact .inr hmiss
  | alloc ht hnin hofs heq =>
    intro hF hdisj'
    subst heq
    rw [hupdate_disj] at hdisj'
    obtain ⟨hdisj, hnin'⟩ := hdisj'
    left
    rw [hupdate_union (hupdate_disj.mpr ⟨hdisj, hnin'⟩)]
    refine ⟨.alloc ht ?_ hofs rfl, hdisj⟩
    simp_all
  | free ht hsome hofs hcov heq =>
    intro hF hdisj'
    subst heq
    rw [hupdate_disj] at hdisj'
    obtain ⟨hdisj, hnin'⟩ := hdisj'
    left
    rw [hupdate_union (hupdate_disj.mpr ⟨hdisj, hnin'⟩)]
    exact ⟨.free ht (PMap.union_apply_some_l hsome) hofs hcov rfl, hdisj⟩
  | freeErr ht hsome =>
    exact fun hF hdisj => .inl ⟨.freeErr ht (PMap.union_apply_some_l hsome), hdisj⟩
  | freeErrBlock ht hofs =>
    exact fun hF hdisj => .inl ⟨.freeErrBlock ht hofs, hdisj⟩
  | freeMiss ht hnin =>
    intro hF hdisj
    rename_i t hh l
    rcases hl : hF l.1 with _ | bv
    · refine .inl ⟨.freeMiss ht ?_, hdisj⟩
      simp_all
    · exact .inr ⟨l, rfl, by simp [hl]⟩
  | freeMissBlock ht hsome hlt hnin =>
    exact fun hF hdisj =>
      .inl ⟨.freeMissBlock ht (PMap.union_apply_some_l hsome) hlt hnin, hdisj⟩
  | store ht₁ ht₂ hsome hdom heq =>
    intro hF hdisj'
    subst heq
    rw [hupdate_disj] at hdisj'
    obtain ⟨hdisj, hnin'⟩ := hdisj'
    left
    rw [hupdate_union (hupdate_disj.mpr ⟨hdisj, hnin'⟩)]
    exact ⟨.store ht₁ ht₂ (PMap.union_apply_some_l hsome) hdom rfl, hdisj⟩
  | storeErr ht hsome =>
    exact fun hF hdisj => .inl ⟨.storeErr ht (PMap.union_apply_some_l hsome), hdisj⟩
  | storeMiss ht hnin =>
    intro hF hdisj
    rename_i t₁ t₂ hh l
    rcases hl : hF l.1 with _ | bv
    · refine .inl ⟨.storeMiss ht ?_, hdisj⟩
      simp_all
    · exact .inr ⟨l, rfl, by simp [hl]⟩
  | storeMissBlock ht hsome hnin =>
    exact fun hF hdisj =>
      .inl ⟨.storeMissBlock ht (PMap.union_apply_some_l hsome) hnin, hdisj⟩
  | load ht hsome hval =>
    exact fun hF hdisj => .inl ⟨.load ht (PMap.union_apply_some_l hsome) hval, hdisj⟩
  | loadErr ht hsome =>
    exact fun hF hdisj => .inl ⟨.loadErr ht (PMap.union_apply_some_l hsome), hdisj⟩
  | loadErrBlock ht hsome hval =>
    exact fun hF hdisj => .inl ⟨.loadErrBlock ht (PMap.union_apply_some_l hsome) hval, hdisj⟩
  | loadMiss ht hnin =>
    intro hF hdisj
    rename_i t hh l
    rcases hl : hF l.1 with _ | bv
    · refine .inl ⟨.loadMiss ht ?_, hdisj⟩
      simp_all
    · exact .inr ⟨l, rfl, by simp [hl]⟩
  | loadMissBlock ht hsome hnin =>
    exact fun hF hdisj =>
      .inl ⟨.loadMissBlock ht (PMap.union_apply_some_l hsome) hnin, hdisj⟩
  | call hf hstep ih =>
    intro hF hdisj'
    rcases ih hF hdisj' with ⟨hstepF, hdisj⟩ | hmiss
    · exact .inl ⟨.call hf hstepF, hdisj⟩
    · exact .inr hmiss

/-- Over-approximate frame validity — `frame_subtraction`. -/
theorem frame_subtraction {γ : ImplCtx} {h e h' ε} (hstep : γ ⊢ ⟨h | e⟩ ⇓ᵢ ⟨h' | ε⟩) :
    ∀ hs hF, h = hs ∪ hF → hs ##ₘ hF →
    ∃ hs', hs' ##ₘ hF ∧
      (((γ ⊢ ⟨hs | e⟩ ⇓ᵢ ⟨hs' | ε⟩) ∧ h' = hs' ∪ hF) ∨
       (∃ l, (γ ⊢ ⟨hs | e⟩ ⇓ᵢ ⟨hs' | .miss l⟩) ∧ l.1 ∈ hF.dom)) := by
  induction hstep with
  | pure hp => exact fun hs hF hheap hdisj => ⟨hs, hdisj, .inl ⟨.pure hp, hheap⟩⟩
  | assume => exact fun hs hF hheap hdisj => ⟨hs, hdisj, .inl ⟨.assume, hheap⟩⟩
  | error => exact fun hs hF hheap hdisj => ⟨hs, hdisj, .inl ⟨.error, hheap⟩⟩
  | letIn hstep₁ hstep₂ ih₁ ih₂ =>
    intro hs hF hheap hdisj
    obtain ⟨hs'', hdisj'', ih₁'⟩ := ih₁ hs hF hheap hdisj
    rcases ih₁' with ⟨hstep₁F, hheap''⟩ | ⟨l, hmiss, hdom⟩
    · obtain ⟨hs', hdisj', ih₂'⟩ := ih₂ hs'' hF hheap'' hdisj''
      rcases ih₂' with ⟨hstep₂F, hheap'⟩ | ⟨l, hmiss, hdom⟩
      · exact ⟨hs', hdisj', .inl ⟨.letIn hstep₁F hstep₂F, hheap'⟩⟩
      · exact ⟨hs', hdisj', .inr ⟨l, .letIn hstep₁F hmiss, hdom⟩⟩
    · exact ⟨hs'', hdisj'', .inr ⟨l, .letCut hmiss (by simp), hdom⟩⟩
  | letCut hstep hne ih =>
    intro hs hF hheap hdisj
    obtain ⟨hs', hdisj', ih'⟩ := ih hs hF hheap hdisj
    rcases ih' with ⟨hstepF, hheap'⟩ | ⟨l, hmiss, hdom⟩
    · exact ⟨hs', hdisj', .inl ⟨.letCut hstepF hne, hheap'⟩⟩
    · exact ⟨hs', hdisj', .inr ⟨l, .letCut hmiss (by simp), hdom⟩⟩
  | choice hstep hor ih =>
    intro hs hF hheap hdisj
    obtain ⟨hs', hdisj', ih'⟩ := ih hs hF hheap hdisj
    rcases ih' with ⟨hstepF, hheap'⟩ | ⟨l, hmiss, hdom⟩
    · exact ⟨hs', hdisj', .inl ⟨.choice hstepF hor, hheap'⟩⟩
    · exact ⟨hs', hdisj', .inr ⟨l, .choice hmiss hor, hdom⟩⟩
  | alloc ht hnin hofs heq =>
    intro hs hF hheap hdisj
    subst heq hheap
    simp only [PMap.dom_union, Set.mem_union, not_or] at hnin
    refine ⟨hstore hs _ _ (balloc _), hupdate_disj.mpr ⟨hdisj, hnin.2⟩,
      .inl ⟨.alloc ht hnin.1 hofs rfl, ?_⟩⟩
    rw [hupdate_union (hupdate_disj.mpr ⟨hdisj, hnin.2⟩)]
  | free ht hsome hofs hcov heq =>
    intro hs hF hheap hdisj
    subst heq hheap
    rcases PMap.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · have hFnone := hdisj.some_l hsome'
      refine ⟨hfree hs _, hupdate_disj.mpr ⟨hdisj, by simp [hFnone]⟩,
        .inl ⟨.free ht hsome' hofs hcov rfl, ?_⟩⟩
      rw [hupdate_union (hupdate_disj.mpr ⟨hdisj, by simp [hFnone]⟩)]
    · exact ⟨hs, hdisj, .inr ⟨_, .freeMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | freeErr ht hsome =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PMap.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.freeErr ht hsome', rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .freeMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | freeErrBlock ht hofs =>
    intro hs hF hheap hdisj
    subst hheap
    exact ⟨hs, hdisj, .inl ⟨.freeErrBlock ht hofs, rfl⟩⟩
  | freeMiss ht hnin =>
    intro hs hF hheap hdisj
    subst hheap
    exact ⟨hs, hdisj, .inl ⟨.freeMiss ht (by simp_all), rfl⟩⟩
  | freeMissBlock ht hsome hlt hnin =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PMap.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.freeMissBlock ht hsome' hlt hnin, rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .freeMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | store ht₁ ht₂ hsome hdom heq =>
    intro hs hF hheap hdisj
    subst heq hheap
    rcases PMap.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · refine ⟨hstore hs _ _ (bupdate _ _ _),
        PMap.disjoint_some_insert _ hsome' hdisj,
        .inl ⟨.store ht₁ ht₂ hsome' hdom rfl, ?_⟩⟩
      exact (hupdate_union (PMap.disjoint_some_insert _ hsome' hdisj)).symm
    · exact ⟨hs, hdisj, .inr ⟨_, .storeMiss ht₁ (by simp [hnone]), by simp [hsome']⟩⟩
  | storeErr ht hsome =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PMap.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.storeErr ht hsome', rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .storeMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | storeMiss ht hnin =>
    intro hs hF hheap hdisj
    subst hheap
    exact ⟨hs, hdisj, .inl ⟨.storeMiss ht (by simp_all), rfl⟩⟩
  | storeMissBlock ht hsome hnin =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PMap.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.storeMissBlock ht hsome' hnin, rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .storeMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | load ht hsome hval =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PMap.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.load ht hsome' hval, rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .loadMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | loadErr ht hsome =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PMap.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.loadErr ht hsome', rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .loadMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | loadErrBlock ht hsome hval =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PMap.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.loadErrBlock ht hsome' hval, rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .loadMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | loadMiss ht hnin =>
    intro hs hF hheap hdisj
    subst hheap
    exact ⟨hs, hdisj, .inl ⟨.loadMiss ht (by simp_all), rfl⟩⟩
  | loadMissBlock ht hsome hnin =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PMap.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.loadMissBlock ht hsome' hnin, rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .loadMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | call hf hstep ih =>
    intro hs hF hheap hdisj
    obtain ⟨hs', hdisj', ih'⟩ := ih hs hF hheap hdisj
    rcases ih' with ⟨hstepF, hheap'⟩ | ⟨l, hmiss, hdom⟩
    · exact ⟨hs', hdisj', .inl ⟨.call hf hstepF, hheap'⟩⟩
    · exact ⟨hs', hdisj', .inr ⟨l, .call hf hmiss, hdom⟩⟩

/-! ### Relating the instrumented and the full semantics -/

/-- `exit_in_full`. -/
def Exit.toFull : Exit → Exit
  | .miss _ => .err
  | ε => ε

@[simp] theorem Exit.toFull_ok (v : Val) : (Exit.ok v).toFull = .ok v := rfl
@[simp] theorem Exit.toFull_err : Exit.err.toFull = .err := rfl
@[simp] theorem Exit.toFull_miss (l : Loc) : (Exit.miss l).toFull = .err := rfl

/-- `semantics_preservation`. -/
theorem semantics_preservation {γ : ImplCtx} {h e h' ε}
    (hstep : γ ⊢ ⟨h | e⟩ ⇓ᵢ ⟨h' | ε⟩) : γ ⊢ ⟨h | e⟩ ⇓ ⟨h' | ε.toFull⟩ := by
  induction hstep with
  | pure hp => exact .pure hp
  | assume => exact .assume
  | error => exact .error
  | letIn _ _ ih₁ ih₂ => exact .letIn ih₁ ih₂
  | letCut _ hne ih =>
    refine .letCut ih ?_
    rintro ⟨v, hv⟩
    exact hne ⟨v, by cases ‹Exit› <;> simp_all [Exit.toFull]⟩
  | choice _ hor ih => exact .choice ih hor
  | alloc ht hnin hofs heq => exact .alloc ht hnin hofs heq
  | free ht hsome hofs hcov heq => exact .free ht hsome hofs hcov heq
  | freeErr ht hsome => exact .freeErr ht hsome
  | freeErrBlock ht hofs => exact .freeErrBlock ht hofs
  | freeMiss ht hnin => exact .freeMiss ht hnin
  | freeMissBlock ht hsome hlt hnin => exact .freeMissBlock ht hsome hlt hnin
  | store ht₁ ht₂ hsome hdom heq => exact .store ht₁ ht₂ hsome hdom heq
  | storeErr ht hsome => exact .storeErr ht hsome
  | storeMiss ht hnin => exact .storeMiss ht hnin
  | storeMissBlock ht hsome hnin => exact .storeMissBlock ht hsome hnin
  | load ht hsome hval => exact .load ht hsome hval
  | loadErr ht hsome => exact .loadErr ht hsome
  | loadErrBlock ht hsome hval => exact .loadErrBlock ht hsome hval
  | loadMiss ht hnin => exact .loadMiss ht hnin
  | loadMissBlock ht hsome hnin => exact .loadMissBlock ht hsome hnin
  | call hf _ ih => exact .call hf ih

end RUXt
