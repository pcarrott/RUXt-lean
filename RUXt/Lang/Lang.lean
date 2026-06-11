/-
Port of `theories/lang/lang.v`: language syntax, pure expression evaluation,
variable substitution.
-/
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Equiv.List
import RUXt.Lib.PMap
import RUXt.Lib.List

namespace RUXt

/-! ### Memory locations -/

/-- Memory blocks (stdpp's `positive`; any countably infinite type works). -/
abbrev Block := ℕ

/-- Memory locations: a block together with an offset into it. -/
abbrev Loc := Block × ℕ

/-- `offset l i` shifts the location `l` by `i` cells (`l +ₗ i`). -/
def Loc.offset (l : Loc) (i : ℕ) : Loc := (l.1, l.2 + i)

@[inherit_doc] scoped infixl:65 " +ₗ " => Loc.offset

/-- `offset_0`. -/
@[simp] theorem Loc.offset_zero (l : Loc) : l +ₗ 0 = l := rfl

/-! ### Language syntax -/

/-- Binders: anonymous or named (stdpp's `binder`). -/
inductive Binder
  | anon
  | named (x : String)
deriving DecidableEq

/-- Language values. -/
inductive Val
  | int (z : ℤ)
  | bool (b : Bool)
  | loc (l : Loc)
  | unit
deriving DecidableEq

/-- Language terms. -/
inductive Term
  | var (x : String)
  | val (v : Val)
deriving DecidableEq

/-- Unary operations. -/
inductive UnOp
  | minus
  | not
deriving DecidableEq

/-- Binary operations. -/
inductive BinOp
  | add
  | le
  | offset
deriving DecidableEq

/-- Pure expressions. -/
inductive Pure
  | term (t : Term)
  | unOp (op : UnOp) (p : Pure)
  | binOp (op : BinOp) (p₁ p₂ : Pure)
deriving DecidableEq

/-- Program expressions. -/
inductive Expr
  | pure (p : Pure)
  | error
  | assume (t : Term)
  | letIn (x : Binder) (e₁ e₂ : Expr)
  | choice (e₁ e₂ : Expr)
  | alloc (t : Term)
  | free (t : Term)
  | store (t₁ t₂ : Term)
  | load (t : Term)
  | call (f : String) (ts : List Term)
deriving DecidableEq

/-! ### Syntactic sugar

The counterparts of the Rocq notations `TVals`, `PVal`, `TInt`, `PAdd`, …. -/

namespace Term

abbrev int (z : ℤ) : Term := .val (.int z)
abbrev bool (b : Bool) : Term := .val (.bool b)
abbrev true : Term := .bool Bool.true
abbrev false : Term := .bool Bool.false
abbrev loc (l : Loc) : Term := .val (.loc l)
abbrev unit : Term := .val .unit

/-- `TVals vs`: a list of values as terms. -/
def ofVals (vs : List Val) : List Term := vs.map .val

/-- `TVars xs`: a list of variables as terms. -/
def ofVars (xs : List String) : List Term := xs.map .var

@[simp] theorem ofVals_nil : ofVals [] = [] := rfl
@[simp] theorem ofVals_cons (v : Val) (vs : List Val) :
    ofVals (v :: vs) = .val v :: ofVals vs := rfl
@[simp] theorem ofVals_append (vs ws : List Val) :
    ofVals (vs ++ ws) = ofVals vs ++ ofVals ws := List.map_append ..
@[simp] theorem ofVals_length (vs : List Val) : (ofVals vs).length = vs.length :=
  List.length_map ..
@[simp] theorem ofVars_nil : ofVars [] = [] := rfl
@[simp] theorem ofVars_cons (x : String) (xs : List String) :
    ofVars (x :: xs) = .var x :: ofVars xs := rfl
@[simp] theorem ofVars_length (xs : List String) : (ofVars xs).length = xs.length :=
  List.length_map ..

end Term

namespace Pure

abbrev val (v : Val) : Pure := .term (.val v)
abbrev var (x : String) : Pure := .term (.var x)
abbrev int (z : ℤ) : Pure := .term (.int z)
abbrev bool (b : Bool) : Pure := .term (.bool b)
abbrev true : Pure := .term .true
abbrev false : Pure := .term .false
abbrev loc (l : Loc) : Pure := .term (.loc l)
abbrev unit : Pure := .term .unit
abbrev minus (p : Pure) : Pure := .unOp .minus p
abbrev not (p : Pure) : Pure := .unOp .not p
abbrev add (p₁ p₂ : Pure) : Pure := .binOp .add p₁ p₂
abbrev le (p₁ p₂ : Pure) : Pure := .binOp .le p₁ p₂
abbrev offset (p₁ p₂ : Pure) : Pure := .binOp .offset p₁ p₂

end Pure

/-! ### Countability

The counterparts of the `Countable` instances of the Rocq development. stdpp's
`Countable` corresponds to Mathlib's `Encodable`; since only the mathematical
content matters here, we provide the `Prop`-valued `Countable` instances, which
are interderivable with `Encodable` using choice. -/

section Countability
open Function

instance : Countable Char := by
  have : Injective Char.toNat := by
    intro a b h
    apply Char.ext
    unfold Char.toNat at h
    exact UInt32.toNat_inj.mp h
  exact this.countable

instance : Countable String := by
  have : Injective String.toList := fun _ _ h => String.ext h
  exact this.countable

private def encodeVal : Val → ℤ ⊕ Bool ⊕ Option Loc
  | .int z => .inl z
  | .bool b => .inr (.inl b)
  | .loc l => .inr (.inr (some l))
  | .unit => .inr (.inr none)

instance : Countable Val := by
  have : Injective encodeVal := by intro v w h; cases v <;> cases w <;> simp_all [encodeVal]
  exact this.countable

instance : Countable Term := by
  have : Injective (fun t : Term => match t with
      | .var x => Sum.inl x
      | .val v => Sum.inr v : Term → String ⊕ Val) := by
    intro t u h; cases t <;> cases u <;> simp_all
  exact this.countable

instance : Countable UnOp := by
  have : Injective (fun op : UnOp => match op with
      | .minus => Bool.false
      | .not => Bool.true) := by
    intro o₁ o₂ h; cases o₁ <;> cases o₂ <;> simp_all
  exact this.countable

instance : Countable BinOp := by
  have : Injective (fun op : BinOp => match op with
      | .add => (0 : ℕ)
      | .le => 1
      | .offset => 2) := by
    intro o₁ o₂ h; cases o₁ <;> cases o₂ <;> simp_all
  exact this.countable

instance : Countable Binder := by
  have : Injective (fun b : Binder => match b with
      | .anon => none
      | .named x => some x) := by
    intro b₁ b₂ h; cases b₁ <;> cases b₂ <;> simp_all
  exact this.countable

private def encodePure (ft : Term → ℕ) (fu : UnOp → ℕ) (fb : BinOp → ℕ) : Pure → ℕ
  | .term t => Nat.pair 0 (ft t)
  | .unOp op p => Nat.pair 1 (Nat.pair (fu op) (encodePure ft fu fb p))
  | .binOp op p₁ p₂ =>
      Nat.pair 2 (Nat.pair (fb op) (Nat.pair (encodePure ft fu fb p₁) (encodePure ft fu fb p₂)))

instance : Countable Pure := by
  obtain ⟨ft, hft⟩ := exists_injective_nat Term
  obtain ⟨fu, hfu⟩ := exists_injective_nat UnOp
  obtain ⟨fb, hfb⟩ := exists_injective_nat BinOp
  have : Injective (encodePure ft fu fb) := by
    intro p q h
    induction p generalizing q <;> cases q <;>
      simp_all [encodePure, Nat.pair_eq_pair, hft.eq_iff, hfu.eq_iff, hfb.eq_iff] <;>
      grind
  exact this.countable

private def encodeExpr (fp : Pure → ℕ) (ft : Term → ℕ) (fts : List Term → ℕ)
    (fb : Binder → ℕ) (fs : String → ℕ) : Expr → ℕ
  | .pure p => Nat.pair 0 (fp p)
  | .error => Nat.pair 1 0
  | .assume t => Nat.pair 2 (ft t)
  | .letIn x e₁ e₂ =>
      Nat.pair 3 (Nat.pair (fb x) (Nat.pair (encodeExpr fp ft fts fb fs e₁)
        (encodeExpr fp ft fts fb fs e₂)))
  | .choice e₁ e₂ =>
      Nat.pair 4 (Nat.pair (encodeExpr fp ft fts fb fs e₁) (encodeExpr fp ft fts fb fs e₂))
  | .alloc t => Nat.pair 5 (ft t)
  | .free t => Nat.pair 6 (ft t)
  | .store t₁ t₂ => Nat.pair 7 (Nat.pair (ft t₁) (ft t₂))
  | .load t => Nat.pair 8 (ft t)
  | .call f ts => Nat.pair 9 (Nat.pair (fs f) (fts ts))

instance : Countable Expr := by
  obtain ⟨fp, hfp⟩ := exists_injective_nat Pure
  obtain ⟨ft, hft⟩ := exists_injective_nat Term
  obtain ⟨fts, hfts⟩ := exists_injective_nat (List Term)
  obtain ⟨fb, hfb⟩ := exists_injective_nat Binder
  obtain ⟨fs, hfs⟩ := exists_injective_nat String
  have : Injective (encodeExpr fp ft fts fb fs) := by
    intro e₁ e₂ h
    induction e₁ generalizing e₂ <;> cases e₂ <;>
      simp_all [encodeExpr, Nat.pair_eq_pair, hfp.eq_iff, hft.eq_iff, hfts.eq_iff,
        hfb.eq_iff, hfs.eq_iff] <;>
      grind
  exact this.countable

end Countability

/-! ### Evaluation -/

/-- Term evaluation `⌊ t ⌋ₜ`. -/
def Term.eval : Term → Option Val
  | .var _ => none
  | .val v => some v

/-- Evaluation of unary operations. -/
def UnOp.eval : UnOp → Val → Option Val
  | .minus, .int z => some (.int (-z))
  | .not, .bool b => some (.bool !b)
  | _, _ => none

/-- Evaluation of binary operations. -/
def BinOp.eval : BinOp → Val → Val → Option Val
  | .add, .int z₁, .int z₂ => some (.int (z₁ + z₂))
  | .le, .int z₁, .int z₂ => some (.bool (decide (z₁ ≤ z₂)))
  | .offset, .loc l, .int z => some (.loc (l +ₗ z.toNat))
  | _, _, _ => none

/-- Evaluation of pure expressions `⌊ p ⌋ₚ`. -/
def Pure.eval : Pure → Option Val
  | .term t => t.eval
  | .unOp op p =>
      match p.eval with
      | some v => op.eval v
      | none => none
  | .binOp op p₁ p₂ =>
      match p₁.eval, p₂.eval with
      | some v₁, some v₂ => op.eval v₁ v₂
      | _, _ => none

@[simp] theorem Term.eval_var (x : String) : (Term.var x).eval = none := rfl
@[simp] theorem Term.eval_val (v : Val) : (Term.val v).eval = some v := rfl
@[simp] theorem Pure.eval_term (t : Term) : (Pure.term t).eval = t.eval := rfl

/-- `pure_neg_Some`. -/
theorem Pure.eval_minus {p : Pure} {z : ℤ} (h : p.eval = some (.int z)) :
    (Pure.minus p).eval = some (.int (-z)) := by
  simp [eval, h, UnOp.eval]

/-- `pure_not_Some`. -/
theorem Pure.eval_not {p : Pure} {b : Bool} (h : p.eval = some (.bool b)) :
    (Pure.not p).eval = some (.bool !b) := by
  simp [eval, h, UnOp.eval]

/-- `pure_plus_Some`. -/
theorem Pure.eval_add {p₁ p₂ : Pure} {z₁ z₂ : ℤ}
    (h₁ : p₁.eval = some (.int z₁)) (h₂ : p₂.eval = some (.int z₂)) :
    (Pure.add p₁ p₂).eval = some (.int (z₁ + z₂)) := by
  simp [eval, h₁, h₂, BinOp.eval]

/-- `pure_le_Some`. -/
theorem Pure.eval_le {p₁ p₂ : Pure} {z₁ z₂ : ℤ}
    (h₁ : p₁.eval = some (.int z₁)) (h₂ : p₂.eval = some (.int z₂)) :
    (Pure.le p₁ p₂).eval = some (.bool (decide (z₁ ≤ z₂))) := by
  simp [eval, h₁, h₂, BinOp.eval]

/-- `pure_offset_Some`. -/
theorem Pure.eval_offset {p₁ p₂ : Pure} {l : Loc} {z : ℤ}
    (h₁ : p₁.eval = some (.loc l)) (h₂ : p₂.eval = some (.int z)) :
    (Pure.offset p₁ p₂).eval = some (.loc (l +ₗ z.toNat)) := by
  simp [eval, h₁, h₂, BinOp.eval]

/-! ### Substitution and closed expressions -/

/-- `closed_term`. -/
def Term.Closed (X : Set String) : Term → Prop
  | .var x => x ∈ X
  | .val _ => True

/-- `subst_in_term`. -/
def Term.subst (T : Term) (x : String) (t : Term) : Term :=
  if T = .var x then t else T

/-- `closed_pure`. -/
def Pure.Closed (X : Set String) : Pure → Prop
  | .term t => t.Closed X
  | .unOp _ p => p.Closed X
  | .binOp _ p₁ p₂ => p₁.Closed X ∧ p₂.Closed X

/-- `subst_in_pure`. -/
def Pure.subst (p : Pure) (x : String) (t : Term) : Pure :=
  match p with
  | .term T => .term (T.subst x t)
  | .unOp op p => .unOp op (p.subst x t)
  | .binOp op p₁ p₂ => .binOp op (p₁.subst x t) (p₂.subst x t)

/-- `closed_expr`. -/
def Expr.Closed (X : Set String) : Expr → Prop
  | .pure p => p.Closed X
  | .error => True
  | .assume t => t.Closed X
  | .letIn bx e₁ e₂ =>
      e₁.Closed X ∧ e₂.Closed (match bx with | .anon => X | .named x => X ∪ {x})
  | .choice e₁ e₂ => e₁.Closed X ∧ e₂.Closed X
  | .alloc t => t.Closed X
  | .free t => t.Closed X
  | .store t₁ t₂ => t₁.Closed X ∧ t₂.Closed X
  | .load t => t.Closed X
  | .call _ ts => ∀ t ∈ ts, t.Closed X

/-- `closed_program`. -/
def Expr.ClosedProgram (e : Expr) : Prop := e.Closed ∅

/-- `subst_in_expr`. -/
def Expr.substTerm (e : Expr) (x : String) (t : Term) : Expr :=
  match e with
  | .pure p => .pure (p.subst x t)
  | .error => .error
  | .assume T => .assume (T.subst x t)
  | .letIn bx e₁ e₂ =>
      .letIn bx (e₁.substTerm x t) (if bx = .named x then e₂ else e₂.substTerm x t)
  | .choice e₁ e₂ => .choice (e₁.substTerm x t) (e₂.substTerm x t)
  | .alloc T => .alloc (T.subst x t)
  | .free T => .free (T.subst x t)
  | .store T₁ T₂ => .store (T₁.subst x t) (T₂.subst x t)
  | .load T => .load (T.subst x t)
  | .call f Ts => .call f (Ts.map (·.subst x t))

/-- `subst`: substitute a value for a binder (`e ⌊ v // bx ⌋`). -/
def Expr.subst (e : Expr) (bx : Binder) (v : Val) : Expr :=
  match bx with
  | .anon => e
  | .named x => e.substTerm x (.val v)

/-- `subst_terms`: simultaneous substitution `e ⌊ ts [//] xs ⌋ₜ`. -/
def Expr.substs (e : Expr) (xs : List String) (ts : List Term) : Expr :=
  (xs.zip ts).foldl (fun e xt => e.substTerm xt.1 xt.2) e

@[simp] theorem Expr.substs_nil_l (e : Expr) (ts : List Term) : e.substs [] ts = e := rfl
@[simp] theorem Expr.substs_nil_r (e : Expr) (xs : List String) : e.substs xs [] = e := by
  simp [substs]
@[simp] theorem Expr.substs_cons (e : Expr) (x : String) (xs : List String)
    (t : Term) (ts : List Term) :
    e.substs (x :: xs) (t :: ts) = (e.substTerm x t).substs xs ts := rfl

/-! ### Properties of substitution -/

/-- `is_closed_term`. -/
theorem Term.Closed.subst_eq {X : Set String} {T : Term} (h : T.Closed X) {x : String}
    (t : Term) (hx : x ∉ X) : T.subst x t = T := by
  cases T <;> simp_all [Term.Closed, Term.subst]
  grind

/-- `is_closed_pure`. -/
theorem Pure.Closed.subst_eq {X : Set String} {p : Pure} (h : p.Closed X) {x : String}
    (t : Term) (hx : x ∉ X) : p.subst x t = p := by
  induction p with
  | term T => exact congrArg _ (Term.Closed.subst_eq h t hx)
  | unOp op p ih => simp_all [Pure.Closed, Pure.subst]
  | binOp op p₁ p₂ ih₁ ih₂ => simp_all [Pure.Closed, Pure.subst]

/-- `is_closed_expr`. -/
theorem Expr.Closed.subst_eq {X : Set String} {e : Expr} (h : e.Closed X) {x : String}
    (t : Term) (hx : x ∉ X) : e.substTerm x t = e := by
  induction e generalizing X with
  | pure p => exact congrArg _ (Pure.Closed.subst_eq h t hx)
  | error => rfl
  | assume T => exact congrArg _ (Term.Closed.subst_eq h t hx)
  | letIn bx e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    have he₂ : (if bx = .named x then e₂ else e₂.substTerm x t) = e₂ := by
      by_cases hbx : bx = .named x
      · simp [hbx]
      · rw [if_neg hbx]
        cases bx with
        | anon => exact ih₂ h₂ hx
        | named y =>
          refine ih₂ h₂ ?_
          intro hmem
          rcases Set.mem_union .. |>.mp hmem with hX | hy
          · exact hx hX
          · rw [Set.mem_singleton_iff] at hy
            exact hbx (by rw [hy])
    simp [Expr.substTerm, ih₁ h₁ hx, he₂]
  | choice e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    simp [Expr.substTerm, ih₁ h₁ hx, ih₂ h₂ hx]
  | alloc T => exact congrArg _ (Term.Closed.subst_eq h t hx)
  | free T => exact congrArg _ (Term.Closed.subst_eq h t hx)
  | store T₁ T₂ =>
    obtain ⟨h₁, h₂⟩ := h
    simp [Expr.substTerm, Term.Closed.subst_eq h₁ t hx, Term.Closed.subst_eq h₂ t hx]
  | load T => exact congrArg _ (Term.Closed.subst_eq h t hx)
  | call f Ts =>
    have : Ts.map (·.subst x t) = Ts.map id :=
      List.map_congr_left fun T hT => Term.Closed.subst_eq (h T hT) t hx
    simp [Expr.substTerm, this]

/-- `is_closed_program`. -/
theorem Expr.ClosedProgram.subst_eq {e : Expr} (h : e.ClosedProgram) (bx : Binder) (v : Val) :
    e.subst bx v = e := by
  cases bx with
  | anon => rfl
  | named x => exact Expr.Closed.subst_eq h _ (by simp)

/-- `subst_vals_subst`. -/
theorem Expr.substs_snoc (e : Expr) {xs : List String} {vs : List Val} (x : String) (v : Val)
    (hlen : xs.length = vs.length) :
    (e.substs xs (Term.ofVals vs)).subst (.named x) v
      = e.substs (xs ++ [x]) (Term.ofVals (vs ++ [v])) := by
  simp only [Expr.subst, Expr.substs, Term.ofVals_append]
  rw [List.zip_append (by simpa using hlen), List.foldl_append]
  rfl

/-- `subst_TVals`. -/
theorem Term.subst_ofVals (x : String) (t : Term) (vs : List Val) :
    (Term.ofVals vs).map (·.subst x t) = Term.ofVals vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp_all [Term.subst]

/-- `subst_TVars`. -/
theorem Term.subst_ofVars (x : String) (t : Term) {xs : List String} (hx : x ∉ xs) :
    (Term.ofVars xs).map (·.subst x t) = Term.ofVars xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp_all [Term.subst]; grind

/-- `subst_call_args`. -/
theorem Expr.substs_call {f : String} {xs : List String} {vs : List Val}
    (hlen : xs.length = vs.length) (hdup : xs.Nodup) :
    (Expr.call f (Term.ofVars xs)).substs xs (Term.ofVals vs)
      = .call f (Term.ofVals vs) := by
  suffices h : ∀ (xs : List String) (acc vs : List Val), xs.length = vs.length → xs.Nodup →
      (Expr.call f (Term.ofVals acc ++ Term.ofVars xs)).substs xs (Term.ofVals vs)
        = .call f (Term.ofVals (acc ++ vs)) by
    simpa using h xs [] vs hlen hdup
  intro xs
  induction xs with
  | nil =>
    intro acc vs hlen _
    obtain rfl : vs = [] := by simpa using hlen.symm
    simp [Term.ofVars]
  | cons x xs ih =>
    intro acc vs hlen hdup
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      simp only [Term.ofVals_cons, Expr.substs_cons]
      have hx : x ∉ xs := (List.nodup_cons.mp hdup).1
      have hsub : (Expr.call f (Term.ofVals acc ++ Term.ofVars (x :: xs))).substTerm x (.val v)
          = .call f (Term.ofVals (acc ++ [v]) ++ Term.ofVars xs) := by
        simp only [Expr.substTerm, Term.ofVars_cons, List.map_append, List.map_cons,
          Term.subst_ofVals, Term.subst_ofVars x _ hx, Term.ofVals_append]
        simp [Term.subst]
      rw [hsub, ih (acc ++ [v]) vs (by simpa using hlen) (List.nodup_cons.mp hdup).2]
      simp

/-- `let_subst`. -/
theorem Expr.substs_letIn {x : String} {xs : List String} {vs : List Val} {e₁ e₂ : Expr}
    (hlen : xs.length = vs.length) (hx : x ∉ xs) (hclosed : e₁.ClosedProgram) :
    (Expr.letIn (.named x) e₁ e₂).substs xs (Term.ofVals vs)
      = .letIn (.named x) e₁ (e₂.substs xs (Term.ofVals vs)) := by
  induction xs generalizing vs e₂ with
  | nil =>
    obtain rfl : vs = [] := by simpa using hlen.symm
    rfl
  | cons y ys ih =>
    cases vs with
    | nil => simp at hlen
    | cons v vs =>
      have hxy : x ≠ y := by rintro rfl; simp at hx
      have hsub : (Expr.letIn (.named x) e₁ e₂).substTerm y (.val v)
          = .letIn (.named x) e₁ (e₂.substTerm y (.val v)) := by
        simp only [Expr.substTerm]
        rw [if_neg (by simpa using hxy), Expr.Closed.subst_eq hclosed _ (by simp)]
      simp only [Term.ofVals_cons, Expr.substs_cons, hsub]
      exact ih (by simpa using hlen) (by simp_all)

end RUXt
