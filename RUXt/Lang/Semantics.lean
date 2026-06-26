import RUXt.Lang.Library

namespace RUXt

open scoped PFun

/-! ### Program states: heaps -/

/-- Heap values: a value or the uninitialised `poison`. -/
inductive HeapValue
  | val (v : Val)
  | poison
deriving DecidableEq
/-- Block heaps: partial maps from offsets to heap values. -/
abbrev BlockHeap := PFun ℕ HeapValue
/-- Block values: a live block of a given size, or a freed block. -/
inductive BlockValue
  | block (sz : ℕ) (bh : BlockHeap)
  | freed
/-- Heaps: partial maps from blocks to block values. -/
abbrev Heap := PFun Block BlockValue
noncomputable instance : Union Heap := ⟨PFun.union⟩

/-- Block `bh` stores value `hv` at index `i`. -/
def BlockHeap.MapsTo (bh : BlockHeap) (i : ℕ) (hv : HeapValue) : Prop :=
  bh i = hv
/-- Create a block heap with `n` cells, all initialised to `hv`. -/
def BlockHeap.replicate (hv : HeapValue) : ℕ → BlockHeap
  | 0 => ∅
  | n + 1 => (replicate hv n).insert n hv
/-- A freshly allocated block heap of `n` uninitialised cells. -/
def BlockHeap.alloc : ℕ → BlockHeap := BlockHeap.replicate .poison
/-- Update a block heap at index `i` with value `v`. -/
def BlockHeap.update (bh : BlockHeap) (i : ℕ) (v : Val) : BlockHeap :=
  bh.insert i (.val v)

/-- Heap `h` stores block `bv` at index `b`. -/
def Heap.MapsTo (h : Heap) (b : Block) (bv : BlockValue) : Prop :=
  h b = bv
/-- Update a heap at block `b` with value `bv`. -/
def Heap.update : Heap → Block → BlockValue → Heap
  | h, b, bv => PFun.insert b bv h
/-- Store ⟨`sz`, `bh`⟩ in the heap at block `b`. -/
abbrev Heap.store (h : Heap) (b : Block) (sz : ℕ) (bh : BlockHeap) : Heap :=
  h.update b (.block sz bh)
/-- Free block `b` from the heap. -/
abbrev Heap.free (h : Heap) (b : Block) : Heap :=
  h.update b .freed

theorem Heap.update_disj {h h' : Heap} {b : Block} {bv : BlockValue} :
    h.update b bv ##ₘ h' ↔ h ##ₘ h' ∧ b ∉ h'.dom := by
  unfold Heap.update
  rw [PFun.disjoint_insert_l]
  simp only [PFun.not_mem_dom]
  exact and_comm

theorem Heap.update_union {h h' : Heap} {b : Block} {bv : BlockValue}
    (_ : h.update b bv ##ₘ h') :
    (h.update b bv) ∪ h' = (h ∪ h').update b bv :=
  PFun.insert_union_l ..

/-! ### Operational semantics

`BigStep` is the full semantics (`Λ ⊢ ⟨h | e⟩ ⇓ ⟨h' | ε⟩`).

`FrameStep` the instrumented semantics (`Λ ⊢ ⟨h | e⟩ ⇓ᵢ ⟨h' | ε⟩`),
which reports misses on locations outside the current heap fragment. -/

/-- Termination tags. -/
inductive Exit
  | ok (v : Val)
  | err
  | miss (l : Loc)
deriving DecidableEq

/-- The full big-step semantics. -/
inductive BigStep (Λ : Library) : Heap → Expr → Heap → Exit → Prop
  | pure {p : Pure} {h : Heap} {v : Val} :
      p.eval = some v →
      BigStep Λ h (.pure p) h (.ok v)
  | assume {h : Heap} :
      BigStep Λ h (.assume .true) h (.ok .unit)
  | error {h : Heap} :
      BigStep Λ h .error h .err
  | letIn {x : Binder} {e₁ e₂ : Expr} {h h' h'' : Heap} {v : Val} {ε : Exit} :
      BigStep Λ h e₁ h'' (.ok v) → BigStep Λ h'' (e₂.subst x v) h' ε →
      BigStep Λ h (.letIn x e₁ e₂) h' ε
  | letCut {x : Binder} {e₁ e₂ : Expr} {h h' : Heap} {ε : Exit} :
      BigStep Λ h e₁ h' ε → (¬ ∃ v, ε = .ok v) →
      BigStep Λ h (.letIn x e₁ e₂) h' ε
  | choice {eᵢ e₁ e₂ : Expr} {h h' : Heap} {ε : Exit} :
      BigStep Λ h eᵢ h' ε → (eᵢ = e₁ ∨ eᵢ = e₂) →
      BigStep Λ h (.choice e₁ e₂) h' ε
  | alloc {t : Term} {h h' : Heap} {l : Loc} {n : ℕ} :
      t.eval = some (.int n) →
      l.1 ∉ h.dom → l.2 = 0 →
      h' = h.store l.1 n (BlockHeap.alloc n) →
      BigStep Λ h (.alloc t) h' (.ok (.loc l))
  | free {t : Term} {h h' : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 (.block sz bh) → l.2 = 0 → (∀ i < sz, i ∈ bh.dom) →
      h' = h.free l.1 →
      BigStep Λ h (.free t) h' (.ok .unit)
  | freeErr {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 .freed →
      BigStep Λ h (.free t) h .err
  | freeErrBlock {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      l.2 ≠ 0 →
      BigStep Λ h (.free t) h .err
  | freeMiss {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      l.1 ∉ h.dom →
      BigStep Λ h (.free t) h .err
  | freeMissBlock {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} {i : ℕ} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 (.block sz bh) → i < sz → i ∉ bh.dom →
      BigStep Λ h (.free t) h .err
  | store {t₁ t₂ : Term} {h h' : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} {v : Val} :
      t₁.eval = some (.loc l) → t₂.eval = some v →
      h.MapsTo l.1 (.block sz bh) → l.2 ∈ bh.dom →
      h' = h.store l.1 sz (bh.update l.2 v) →
      BigStep Λ h (.store t₁ t₂) h' (.ok .unit)
  | storeErr {t₁ t₂ : Term} {h : Heap} {l : Loc} :
      t₁.eval = some (.loc l) →
      h.MapsTo l.1 .freed →
      BigStep Λ h (.store t₁ t₂) h .err
  | storeMiss {t₁ t₂ : Term} {h : Heap} {l : Loc} :
      t₁.eval = some (.loc l) →
      l.1 ∉ h.dom →
      BigStep Λ h (.store t₁ t₂) h .err
  | storeMissBlock {t₁ t₂ : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t₁.eval = some (.loc l) →
      h.MapsTo l.1 (.block sz bh) → l.2 ∉ bh.dom →
      BigStep Λ h (.store t₁ t₂) h .err
  | load {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} {v : Val} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 (.block sz bh) → bh.MapsTo l.2 (.val v) →
      BigStep Λ h (.load t) h (.ok v)
  | loadErr {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 .freed →
      BigStep Λ h (.load t) h .err
  | loadErrBlock {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 (.block sz bh) → bh.MapsTo l.2 .poison →
      BigStep Λ h (.load t) h .err
  | loadMiss {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      l.1 ∉ h.dom →
      BigStep Λ h (.load t) h .err
  | loadMissBlock {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 (.block sz bh) → l.2 ∉ bh.dom →
      BigStep Λ h (.load t) h .err
  | call {f : Fid} {xs e τ P} {ts : List Term} {h h' : Heap} {ε : Exit} :
      Λ.MapsTo f ⟨xs, e, τ, P⟩ → BigStep Λ h (e.substs (xs.map Prod.fst) ts) h' ε →
      BigStep Λ h (.call f ts) h' ε

@[inherit_doc] scoped notation:50 Λ:51 " ⊢ " "⟨" h " | " e "⟩" " ⇓ " "⟨" h' " | " ε "⟩" =>
  BigStep Λ h e h' ε

/-- The instrumented big-step semantics. -/
inductive FrameStep (Λ : Library) : Heap → Expr → Heap → Exit → Prop
  | pure {p : Pure} {h : Heap} {v : Val} :
      p.eval = some v →
      FrameStep Λ h (.pure p) h (.ok v)
  | assume {h : Heap} :
      FrameStep Λ h (.assume .true) h (.ok .unit)
  | error {h : Heap} :
      FrameStep Λ h .error h .err
  | letIn {x : Binder} {e₁ e₂ : Expr} {h h' h'' : Heap} {v : Val} {ε : Exit} :
      FrameStep Λ h e₁ h'' (.ok v) → FrameStep Λ h'' (e₂.subst x v) h' ε →
      FrameStep Λ h (.letIn x e₁ e₂) h' ε
  | letCut {x : Binder} {e₁ e₂ : Expr} {h h' : Heap} {ε : Exit} :
      FrameStep Λ h e₁ h' ε → (¬ ∃ v, ε = .ok v) →
      FrameStep Λ h (.letIn x e₁ e₂) h' ε
  | choice {eᵢ e₁ e₂ : Expr} {h h' : Heap} {ε : Exit} :
      FrameStep Λ h eᵢ h' ε → (eᵢ = e₁ ∨ eᵢ = e₂) →
      FrameStep Λ h (.choice e₁ e₂) h' ε
  | alloc {t : Term} {h h' : Heap} {l : Loc} {n : ℕ} :
      t.eval = some (.int n) →
      l.1 ∉ h.dom → l.2 = 0 →
      h' = h.store l.1 n (BlockHeap.alloc n) →
      FrameStep Λ h (.alloc t) h' (.ok (.loc l))
  | free {t : Term} {h h' : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 (.block sz bh) → l.2 = 0 → (∀ i < sz, i ∈ bh.dom) →
      h' = h.free l.1 →
      FrameStep Λ h (.free t) h' (.ok .unit)
  | freeErr {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 .freed →
      FrameStep Λ h (.free t) h .err
  | freeErrBlock {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      l.2 ≠ 0 →
      FrameStep Λ h (.free t) h .err
  | freeMiss {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      l.1 ∉ h.dom →
      FrameStep Λ h (.free t) h (.miss l)
  | freeMissBlock {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} {i : ℕ} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 (.block sz bh) → i < sz → i ∉ bh.dom →
      FrameStep Λ h (.free t) h (.miss (l +ₗ i))
  | store {t₁ t₂ : Term} {h h' : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} {v : Val} :
      t₁.eval = some (.loc l) → t₂.eval = some v →
      h.MapsTo l.1 (.block sz bh) → l.2 ∈ bh.dom →
      h' = h.store l.1 sz (bh.update l.2 v) →
      FrameStep Λ h (.store t₁ t₂) h' (.ok .unit)
  | storeErr {t₁ t₂ : Term} {h : Heap} {l : Loc} :
      t₁.eval = some (.loc l) →
      h.MapsTo l.1 .freed →
      FrameStep Λ h (.store t₁ t₂) h .err
  | storeMiss {t₁ t₂ : Term} {h : Heap} {l : Loc} :
      t₁.eval = some (.loc l) →
      l.1 ∉ h.dom →
      FrameStep Λ h (.store t₁ t₂) h (.miss l)
  | storeMissBlock {t₁ t₂ : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t₁.eval = some (.loc l) →
      h.MapsTo l.1 (.block sz bh) → l.2 ∉ bh.dom →
      FrameStep Λ h (.store t₁ t₂) h (.miss l)
  | load {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} {v : Val} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 (.block sz bh) → bh.MapsTo l.2 (.val v) →
      FrameStep Λ h (.load t) h (.ok v)
  | loadErr {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 .freed →
      FrameStep Λ h (.load t) h .err
  | loadErrBlock {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 (.block sz bh) → bh.MapsTo l.2 .poison →
      FrameStep Λ h (.load t) h .err
  | loadMiss {t : Term} {h : Heap} {l : Loc} :
      t.eval = some (.loc l) →
      l.1 ∉ h.dom →
      FrameStep Λ h (.load t) h (.miss l)
  | loadMissBlock {t : Term} {h : Heap} {l : Loc} {sz : ℕ} {bh : BlockHeap} :
      t.eval = some (.loc l) →
      h.MapsTo l.1 (.block sz bh) → l.2 ∉ bh.dom →
      FrameStep Λ h (.load t) h (.miss l)
  | call {f : Fid} {xs e τ P} {ts : List Term} {h h' : Heap} {ε : Exit} :
      Λ.MapsTo f ⟨xs, e, τ, P⟩ → FrameStep Λ h (e.substs (xs.map Prod.fst) ts) h' ε →
      FrameStep Λ h (.call f ts) h' ε

@[inherit_doc] scoped notation:50 Λ:51 " ⊢ " "⟨" h " | " e "⟩" " ⇓ᵢ " "⟨" h' " | " ε "⟩" =>
  FrameStep Λ h e h' ε

/-! ### Frame properties -/

/-- Frame addition: under-approximate frame validity. -/
theorem frame_addition {Λ : Library} {h e h' ε} (hstep : Λ ⊢ ⟨h | e⟩ ⇓ᵢ ⟨h' | ε⟩) :
    ∀ hF, h' ##ₘ hF →
    ((Λ ⊢ ⟨h ∪ hF | e⟩ ⇓ᵢ ⟨h' ∪ hF | ε⟩) ∧ h ##ₘ hF) ∨
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
    rw [Heap.update_disj] at hdisj'
    obtain ⟨hdisj, hnin'⟩ := hdisj'
    left
    rw [Heap.update_union (Heap.update_disj.mpr ⟨hdisj, hnin'⟩)]
    refine ⟨.alloc ht ?_ hofs rfl, hdisj⟩
    simp_all
  | free ht hsome hofs hcov heq =>
    intro hF hdisj'
    subst heq
    rw [Heap.update_disj] at hdisj'
    obtain ⟨hdisj, hnin'⟩ := hdisj'
    left
    rw [Heap.update_union (Heap.update_disj.mpr ⟨hdisj, hnin'⟩)]
    exact ⟨.free ht (PFun.union_apply_some_l hsome) hofs hcov rfl, hdisj⟩
  | freeErr ht hsome =>
    exact fun hF hdisj => .inl ⟨.freeErr ht (PFun.union_apply_some_l hsome), hdisj⟩
  | freeErrBlock ht hofs =>
    exact fun hF hdisj => .inl ⟨.freeErrBlock ht hofs, hdisj⟩
  | freeMiss ht hnin =>
    intro hF hdisj
    rename_i t hh l
    by_cases hl : l.1 ∈ hF.dom
    · exact .inr ⟨l, rfl, hl⟩
    · refine .inl ⟨.freeMiss ht ?_, hdisj⟩
      simp_all
  | freeMissBlock ht hsome hlt hnin =>
    exact fun hF hdisj =>
      .inl ⟨.freeMissBlock ht (PFun.union_apply_some_l hsome) hlt hnin, hdisj⟩
  | store ht₁ ht₂ hsome hdom heq =>
    intro hF hdisj'
    subst heq
    rw [Heap.update_disj] at hdisj'
    obtain ⟨hdisj, hnin'⟩ := hdisj'
    left
    rw [Heap.update_union (Heap.update_disj.mpr ⟨hdisj, hnin'⟩)]
    exact ⟨.store ht₁ ht₂ (PFun.union_apply_some_l hsome) hdom rfl, hdisj⟩
  | storeErr ht hsome =>
    exact fun hF hdisj => .inl ⟨.storeErr ht (PFun.union_apply_some_l hsome), hdisj⟩
  | storeMiss ht hnin =>
    intro hF hdisj
    rename_i t₁ t₂ hh l
    by_cases hl : l.1 ∈ hF.dom
    · exact .inr ⟨l, rfl, hl⟩
    · refine .inl ⟨.storeMiss ht ?_, hdisj⟩
      simp_all
  | storeMissBlock ht hsome hnin =>
    exact fun hF hdisj =>
      .inl ⟨.storeMissBlock ht (PFun.union_apply_some_l hsome) hnin, hdisj⟩
  | load ht hsome hval =>
    exact fun hF hdisj => .inl ⟨.load ht (PFun.union_apply_some_l hsome) hval, hdisj⟩
  | loadErr ht hsome =>
    exact fun hF hdisj => .inl ⟨.loadErr ht (PFun.union_apply_some_l hsome), hdisj⟩
  | loadErrBlock ht hsome hval =>
    exact fun hF hdisj => .inl ⟨.loadErrBlock ht (PFun.union_apply_some_l hsome) hval, hdisj⟩
  | loadMiss ht hnin =>
    intro hF hdisj
    rename_i t hh l
    by_cases hl : l.1 ∈ hF.dom
    · exact .inr ⟨l, rfl, hl⟩
    · refine .inl ⟨.loadMiss ht ?_, hdisj⟩
      simp_all
  | loadMissBlock ht hsome hnin =>
    exact fun hF hdisj =>
      .inl ⟨.loadMissBlock ht (PFun.union_apply_some_l hsome) hnin, hdisj⟩
  | call hf hstep ih =>
    intro hF hdisj'
    rcases ih hF hdisj' with ⟨hstepF, hdisj⟩ | hmiss
    · exact .inl ⟨.call hf hstepF, hdisj⟩
    · exact .inr hmiss

/-- Frame subtraction: over-approximate frame validity. -/
theorem frame_subtraction {Λ : Library} {h e h' ε} (hstep : Λ ⊢ ⟨h | e⟩ ⇓ᵢ ⟨h' | ε⟩) :
    ∀ hs hF, h = hs ∪ hF → hs ##ₘ hF →
    ∃ hs', hs' ##ₘ hF ∧
      (((Λ ⊢ ⟨hs | e⟩ ⇓ᵢ ⟨hs' | ε⟩) ∧ h' = hs' ∪ hF) ∨
       (∃ l, (Λ ⊢ ⟨hs | e⟩ ⇓ᵢ ⟨hs' | .miss l⟩) ∧ l.1 ∈ hF.dom)) := by
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
    rw [PFun.dom_union, Set.mem_union, not_or] at hnin
    refine ⟨hs.store _ _ (BlockHeap.alloc _), Heap.update_disj.mpr ⟨hdisj, hnin.2⟩,
      .inl ⟨.alloc ht hnin.1 hofs rfl, ?_⟩⟩
    rw [Heap.update_union (Heap.update_disj.mpr ⟨hdisj, hnin.2⟩)]
  | free ht hsome hofs hcov heq =>
    intro hs hF hheap hdisj
    subst heq hheap
    rcases PFun.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · have hFnone := hdisj.some_l hsome'
      refine ⟨hs.free _, Heap.update_disj.mpr ⟨hdisj, by simp [hFnone]⟩,
        .inl ⟨.free ht hsome' hofs hcov rfl, ?_⟩⟩
      rw [Heap.update_union (Heap.update_disj.mpr ⟨hdisj, by simp [hFnone]⟩)]
    · exact ⟨hs, hdisj, .inr ⟨_, .freeMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | freeErr ht hsome =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PFun.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
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
    rcases PFun.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.freeMissBlock ht hsome' hlt hnin, rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .freeMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | store ht₁ ht₂ hsome hdom heq =>
    intro hs hF hheap hdisj
    subst heq hheap
    rcases PFun.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · refine ⟨hs.store _ _ (BlockHeap.update _ _ _),
        PFun.disjoint_some_insert _ hsome' hdisj,
        .inl ⟨.store ht₁ ht₂ hsome' hdom rfl, ?_⟩⟩
      exact (Heap.update_union (PFun.disjoint_some_insert _ hsome' hdisj)).symm
    · exact ⟨hs, hdisj, .inr ⟨_, .storeMiss ht₁ (by simp [hnone]), by simp [hsome']⟩⟩
  | storeErr ht hsome =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PFun.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.storeErr ht hsome', rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .storeMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | storeMiss ht hnin =>
    intro hs hF hheap hdisj
    subst hheap
    exact ⟨hs, hdisj, .inl ⟨.storeMiss ht (by simp_all), rfl⟩⟩
  | storeMissBlock ht hsome hnin =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PFun.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.storeMissBlock ht hsome' hnin, rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .storeMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | load ht hsome hval =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PFun.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.load ht hsome' hval, rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .loadMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | loadErr ht hsome =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PFun.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.loadErr ht hsome', rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .loadMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | loadErrBlock ht hsome hval =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PFun.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.loadErrBlock ht hsome' hval, rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .loadMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | loadMiss ht hnin =>
    intro hs hF hheap hdisj
    subst hheap
    exact ⟨hs, hdisj, .inl ⟨.loadMiss ht (by simp_all), rfl⟩⟩
  | loadMissBlock ht hsome hnin =>
    intro hs hF hheap hdisj
    subst hheap
    rcases PFun.union_apply_eq_some.mp hsome with hsome' | ⟨hnone, hsome'⟩
    · exact ⟨hs, hdisj, .inl ⟨.loadMissBlock ht hsome' hnin, rfl⟩⟩
    · exact ⟨hs, hdisj, .inr ⟨_, .loadMiss ht (by simp [hnone]), by simp [hsome']⟩⟩
  | call hf hstep ih =>
    intro hs hF hheap hdisj
    obtain ⟨hs', hdisj', ih'⟩ := ih hs hF hheap hdisj
    rcases ih' with ⟨hstepF, hheap'⟩ | ⟨l, hmiss, hdom⟩
    · exact ⟨hs', hdisj', .inl ⟨.call hf hstepF, hheap'⟩⟩
    · exact ⟨hs', hdisj', .inr ⟨l, .call hf hmiss, hdom⟩⟩

/-! ### Relating the instrumented and the full semantics -/

/-- Maps a `miss` tag to `err`. -/
def Exit.toFull : Exit → Exit
  | .miss _ => .err
  | ε => ε

@[simp] theorem Exit.toFull_ok (v : Val) : (Exit.ok v).toFull = .ok v := rfl
@[simp] theorem Exit.toFull_err : Exit.err.toFull = .err := rfl
@[simp] theorem Exit.toFull_miss (l : Loc) : (Exit.miss l).toFull = .err := rfl

/-- Preserved behaviour between the instrumented and the full semantics. -/
theorem semantics_preservation {Λ : Library} {h e h' ε}
    (hstep : Λ ⊢ ⟨h | e⟩ ⇓ᵢ ⟨h' | ε⟩) : Λ ⊢ ⟨h | e⟩ ⇓ ⟨h' | ε.toFull⟩ := by
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
