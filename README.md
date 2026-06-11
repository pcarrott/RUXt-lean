# RUXt: Lean 4 port

This is a Lean 4 port of the Rocq (Coq) development in `../ruxt-model`. It
proves the same theorems as the original — culminating in the **inadequacy**
theorem for the type refutation algorithm (`RUXt/Model/Refute.lean`) and the
**type unsoundness** theorem relating OX and UX reasoning
(`RUXt/Types/Validity.lean`) — with definitions adapted to idiomatic Lean where
appropriate (see *Design notes* below).

Building requires [Lean 4](https://lean-lang.org) (via `elan`) and downloads
[Mathlib](https://github.com/leanprover-community/mathlib4); to compile, run

```sh
lake exe cache get   # fetch the Mathlib build cache (first time only)
lake build
```

The current proof status is tracked in [`PROGRESS.md`](PROGRESS.md).

### Directory structure

The module layout mirrors the Rocq development one-to-one:

| Rocq (`theories/`) | Lean (`RUXt/`) | Contents |
|---|---|---|
| `lib/list.v` | `Lib/List.lean` | Additional facts about lists (mostly restated from Mathlib). |
| `lib/gmap.v` | `Lib/PMap.lean` | Partial maps (`PMap`) replacing stdpp's `gmap`, with the union/disjointness theory used throughout. |
| `lang/lang.v` | `Lang/Lang.lean` | Language syntax, pure expression evaluation, variable substitution. |
| `lang/semantics.v` | `Lang/Semantics.lean` | Operational semantics (full `⇓` and instrumented `⇓ᵢ`), frame preservation. |
| `lang/assertion.v` | `Lang/Assertion.lean` | Logical assertions on heaps (`Asrt`, `hprop`). |
| `model/logic.v` | `Model/Logic.lean` | Template for a sound under-approximate program logic. |
| `model/risl.v` | `Model/RISL.lean` | RISL proof rules, instantiation as UX logic. |
| `model/typechecker.v` | `Model/TypeChecker.lean` | Function type signatures and safe programs. |
| `model/summary.v` | `Model/Summary.lean` | Summary contexts and properties. |
| `model/refute.v` | `Model/Refute.lean` | The refutation algorithm and the inadequacy theorem. |
| `types/type.v` | `Types/Ty.lean` | Generic type definition, assertions for type ownership. |
| `types/lib/*.v` | `Types/Lib/*.lean` | Default type definitions (`int`, `bool`, `unit`, `own`). |
| `types/rules.v` | `Types/Rules.lean` | Rules of the type system, OX soundness. |
| `types/validity.v` | `Types/Validity.lean` | Properties relating OX and UX reasoning. |

### Name correspondence

Rocq names are kept close to the original up to Lean naming conventions
(`UpperCamelCase` for types and props, `lowerCamelCase` for functions,
`snake_case` for theorems). Every Lean declaration carries a docstring naming
its Rocq counterpart when the name differs, e.g. `frame_addition`,
`spec_soundness`, `judg_soundness`, `inadequacy`, `type_unsoundness` keep their
names, while `eval_expr` ↦ `BigStep`, `eval_expr_frame` ↦ `FrameStep`,
`wf_spec` ↦ `WfSpec`, `asrt` ↦ `Asrt`, etc. Notations (`l +ₗ i`, `⇓`/`⇓ᵢ`,
`∗`, `l ↦ v`, `⌞P⌟`, `⌜P⌝`, `Γ ⊢ ⌈P⌉ e ⌈ε, Q⌉`, `γ ≺ₛ Γ`, `v ⊲ τ`, `[∗ₜ 𝕋]`)
follow the Rocq notations.

### Design notes (Rocq → Lean adaptations)

* **Partial maps instead of finite maps.** The Rocq development uses stdpp's
  `gmap`. Finiteness of the maps plays no role anywhere in the proofs
  (allocation is specified relationally, and no fresh location is ever
  computed), so the Lean port models heaps and contexts as extensional partial
  functions `PMap α β := α → Option β` with left-biased union (`Lib/PMap.lean`).
* **Total contexts.** The contexts that the Rocq development accesses only
  through the total lookup `!!!` (defaulting to `[]` resp. the `unit` type) —
  specification contexts, summary contexts and interpretation contexts — are
  total functions (`SpecCtx := String → List FunSpec`,
  `SummCtx := Tid → List Summary`, `InterpCtx := Tid → Ty`). The
  `lookup_total_*` lemmas are ported against `Function.update`.
* **Flattened summary contexts.** `flat_summ_ctx` is built with `map_fold` in
  Rocq, and its only specification is the membership lemma `elem_of_flat`. The
  port uses the set of entries `flatSummCtx : SummCtx → Set (Tid × Summary)`,
  for which `elem_of_flat` holds definitionally; `valid_context` quantifies the
  chosen sub-context `S' : List (Tid × Summary)` over that set, exactly as the
  Rocq `Σ' ⊆ flat_summ_ctx Σ` does. Likewise `to_type_ctx` (a `map_fold` in
  Rocq) is defined pointwise, with `lookup_type_sign_Some` as its
  specification.
* **Countability.** stdpp's `Countable` is Mathlib's `Encodable`; since only
  the mathematical content matters here, the port provides the `Prop`-valued
  `Countable` instances (interderivable with `Encodable` using choice).
* **`gset string` ↦ `Set String`** for the closedness predicates (finiteness
  of the variable sets is likewise never used).
* **Universes.** `Asrt` quantifies over arbitrary small types (`Asrt.ex`), so
  it lives in `Type 1`, as do the structures containing assertions
  (`Logic`, `FunSpec`, `ConcreteSummary`, `Ty`, …). This matches the implicit
  universe bumps in the Rocq development.

## AI Disclosure

This project was ported from Rocq to Lean using Anthropic Fable 5,
and some proofs were completed using Harmonic's Aristotle.