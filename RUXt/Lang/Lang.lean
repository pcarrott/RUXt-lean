import Mathlib.Data.Set.Insert

namespace RUXt

/-! ### Memory locations -/

/-- Memory blocks. -/
abbrev Block := ℕ
/-- Memory locations: a block together with an offset into it. -/
abbrev Loc := Block × ℕ
/-- `offset l i` shifts the location `l` by `i` cells (`l +ₗ i`). -/
def Loc.offset (l : Loc) (i : ℕ) : Loc := (l.1, l.2 + i)
@[inherit_doc] scoped infixl:65 " +ₗ " => Loc.offset

/-- The offset of a location by zero is the location itself. -/
@[simp] theorem Loc.offset_zero (l : Loc) : l +ₗ 0 = l := rfl

/-! ### Language syntax -/

/-- Program variables -/
abbrev PVar := String
/-- Binders: anonymous or named. -/
inductive Binder
  | anon
  | named (x : PVar)
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
  | var (x : PVar)
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

/-- Function identifiers. -/
abbrev Fid := String
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
  | call (f : Fid) (ts : List Term)
deriving DecidableEq

/-! ### Syntactic sugar -/

namespace Term

abbrev int (z : ℤ) : Term := .val (.int z)
abbrev bool (b : Bool) : Term := .val (.bool b)
abbrev true : Term := .bool Bool.true
abbrev false : Term := .bool Bool.false
abbrev loc (l : Loc) : Term := .val (.loc l)
abbrev unit : Term := .val .unit

/-- A list of values as terms. -/
def ofVals (vs : List Val) : List Term := vs.map .val
/-- A list of variables as terms. -/
def ofVars (xs : List PVar) : List Term := xs.map .var

@[simp] theorem ofVals_nil : ofVals [] = [] := rfl
@[simp] theorem ofVals_cons (v : Val) (vs : List Val) :
    ofVals (v :: vs) = .val v :: ofVals vs := rfl
@[simp] theorem ofVals_append (vs ws : List Val) :
    ofVals (vs ++ ws) = ofVals vs ++ ofVals ws := List.map_append ..
@[simp] theorem ofVals_length (vs : List Val) : (ofVals vs).length = vs.length :=
  List.length_map ..
@[simp] theorem ofVars_nil : ofVars [] = [] := rfl
@[simp] theorem ofVars_cons (x : PVar) (xs : List PVar) :
    ofVars (x :: xs) = .var x :: ofVars xs := rfl
@[simp] theorem ofVars_length (xs : List PVar) : (ofVars xs).length = xs.length :=
  List.length_map ..

end Term

namespace Pure

abbrev val (v : Val) : Pure := .term (.val v)
abbrev var (x : PVar) : Pure := .term (.var x)
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

namespace Expr

abbrev val (v : Val) : Expr := .pure (.val v)
abbrev var (x : PVar) : Expr := .pure (.var x)
abbrev int (z : ℤ) : Expr := .pure (.int z)
abbrev bool (b : Bool) : Expr := .pure (.bool b)
abbrev true : Expr := .pure .true
abbrev false : Expr := .pure .false
abbrev loc (l : Loc) : Expr := .pure (.loc l)
abbrev unit : Expr := .pure .unit

end Expr

/-! ### Evaluation -/

/-- Term evaluation (`⌊ t ⌋ₜ`). -/
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

/-- Evaluation of pure expressions (`⌊ p ⌋ₚ`). -/
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

@[simp] theorem Term.eval_var (x : PVar) : (Term.var x).eval = none := rfl
@[simp] theorem Term.eval_val (v : Val) : (Term.val v).eval = some v := rfl
@[simp] theorem Pure.eval_term (t : Term) : (Pure.term t).eval = t.eval := rfl

theorem Pure.eval_minus {p : Pure} {z : ℤ} (h : p.eval = some (.int z)) :
    (Pure.minus p).eval = some (.int (-z)) := by
  simp [eval, h, UnOp.eval]

theorem Pure.eval_not {p : Pure} {b : Bool} (h : p.eval = some (.bool b)) :
    (Pure.not p).eval = some (.bool !b) := by
  simp [eval, h, UnOp.eval]

theorem Pure.eval_add {p₁ p₂ : Pure} {z₁ z₂ : ℤ}
    (h₁ : p₁.eval = some (.int z₁)) (h₂ : p₂.eval = some (.int z₂)) :
    (Pure.add p₁ p₂).eval = some (.int (z₁ + z₂)) := by
  simp [eval, h₁, h₂, BinOp.eval]

theorem Pure.eval_le {p₁ p₂ : Pure} {z₁ z₂ : ℤ}
    (h₁ : p₁.eval = some (.int z₁)) (h₂ : p₂.eval = some (.int z₂)) :
    (Pure.le p₁ p₂).eval = some (.bool (decide (z₁ ≤ z₂))) := by
  simp [eval, h₁, h₂, BinOp.eval]

theorem Pure.eval_offset {p₁ p₂ : Pure} {l : Loc} {z : ℤ}
    (h₁ : p₁.eval = some (.loc l)) (h₂ : p₂.eval = some (.int z)) :
    (Pure.offset p₁ p₂).eval = some (.loc (l +ₗ z.toNat)) := by
  simp [eval, h₁, h₂, BinOp.eval]

/-! ### Substitution and closed expressions -/

def Term.Closed (X : Set PVar) : Term → Prop
  | .var x => x ∈ X
  | .val _ => True

def Term.subst (T : Term) (x : PVar) (t : Term) : Term :=
  if T = .var x then t else T

def Pure.Closed (X : Set PVar) : Pure → Prop
  | .term t => t.Closed X
  | .unOp _ p => p.Closed X
  | .binOp _ p₁ p₂ => p₁.Closed X ∧ p₂.Closed X

def Pure.subst (p : Pure) (x : PVar) (t : Term) : Pure :=
  match p with
  | .term T => .term (T.subst x t)
  | .unOp op p => .unOp op (p.subst x t)
  | .binOp op p₁ p₂ => .binOp op (p₁.subst x t) (p₂.subst x t)

def Expr.Closed (X : Set PVar) : Expr → Prop
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

def Expr.ClosedProgram (e : Expr) : Prop := e.Closed ∅

def Expr.substTerm (e : Expr) (x : PVar) (t : Term) : Expr :=
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

/-- Substitute a value for a binder (`e ⌊ v // bx ⌋`). -/
def Expr.subst (e : Expr) (bx : Binder) (v : Val) : Expr :=
  match bx with
  | .anon => e
  | .named x => e.substTerm x (.val v)

/-- Substitution by a list of terms (`e ⌊ ts [//] xs ⌋ₜ`). -/
def Expr.substs (e : Expr) (xs : List PVar) (ts : List Term) : Expr :=
  (xs.zip ts).foldl (fun e xt => e.substTerm xt.1 xt.2) e

@[simp] theorem Expr.substs_nil_l (e : Expr) (ts : List Term) : e.substs [] ts = e := rfl
@[simp] theorem Expr.substs_nil_r (e : Expr) (xs : List PVar) : e.substs xs [] = e := by
  simp [substs]
@[simp] theorem Expr.substs_cons (e : Expr) (x : PVar) (xs : List PVar)
    (t : Term) (ts : List Term) :
    e.substs (x :: xs) (t :: ts) = (e.substTerm x t).substs xs ts := rfl

theorem Term.Closed.subst_eq {X : Set PVar} {T : Term} (h : T.Closed X) {x : PVar}
    (t : Term) (hx : x ∉ X) : T.subst x t = T := by
  cases T <;> simp_all [Term.Closed, Term.subst]
  grind

theorem Pure.Closed.subst_eq {X : Set PVar} {p : Pure} (h : p.Closed X) {x : PVar}
    (t : Term) (hx : x ∉ X) : p.subst x t = p := by
  induction p with
  | term T => exact congrArg _ (Term.Closed.subst_eq h t hx)
  | unOp op p ih => simp_all [Pure.Closed, Pure.subst]
  | binOp op p₁ p₂ ih₁ ih₂ => simp_all [Pure.Closed, Pure.subst]

theorem Expr.Closed.subst_eq {X : Set PVar} {e : Expr} (h : e.Closed X) {x : PVar}
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

theorem Expr.ClosedProgram.subst_eq {e : Expr} (h : e.ClosedProgram) (bx : Binder) (v : Val) :
    e.subst bx v = e := by
  cases bx with
  | anon => rfl
  | named x => exact Expr.Closed.subst_eq h _ (by simp)

theorem Expr.substs_snoc (e : Expr) {xs : List PVar} {vs : List Val} (x : PVar) (v : Val)
    (hlen : xs.length = vs.length) :
    (e.substs xs (Term.ofVals vs)).subst (.named x) v
      = e.substs (xs ++ [x]) (Term.ofVals (vs ++ [v])) := by
  simp only [Expr.subst, Expr.substs, Term.ofVals_append]
  rw [List.zip_append (by simpa using hlen), List.foldl_append]
  rfl

theorem Term.subst_ofVals (x : PVar) (t : Term) (vs : List Val) :
    (Term.ofVals vs).map (·.subst x t) = Term.ofVals vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp_all [Term.subst]

theorem Term.subst_ofVars (x : PVar) (t : Term) {xs : List PVar} (hx : x ∉ xs) :
    (Term.ofVars xs).map (·.subst x t) = Term.ofVars xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp_all [Term.subst]; grind

theorem Expr.substs_call {f : Fid} {xs : List PVar} {vs : List Val}
    (hlen : xs.length = vs.length) (hdup : xs.Nodup) :
    (Expr.call f (Term.ofVars xs)).substs xs (Term.ofVals vs)
      = .call f (Term.ofVals vs) := by
  suffices h : ∀ (xs : List PVar) (acc vs : List Val), xs.length = vs.length → xs.Nodup →
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

theorem Expr.substs_letIn {x : PVar} {xs : List PVar} {vs : List Val} {e₁ e₂ : Expr}
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
