# Paper 16: actual numerical syntax equality and finite-binder typed/window reflection

Supporting source scope: `foundations.tex` 3–28, 36–53, 57–90;
`ordinals.tex` 13–28, 30–32, 69–76. This packet supplies exact executable
literal equality and bound-stack/window admission tests for later finite
class and arithmetic work. No result about primary equivalence decision,
least class representatives, arithmetic definability, or ID1 is asserted.

- **Actual literal equality.** `NumberedWindowLiteralEquality` checks
  the frozen `NTerm/NArgs` constructors and every literal field. Free
  names include both global type and Nat name; bound variables include
  type and actual de Bruijn index. Binders, bottom and aux app carry all
  actual annotations. Numbered heads compare the original declared head,
  current output type, finite label, literal base list and ordered extras.
  Ordinary heads use actual literal head equality, not class rank.
  Argument lists preserve order. The target is equality in the existing
  raw syntax, not beta equality, primary equivalence or any weakened
  identity. De Bruijn binding already implements bound-alpha naming.
- **Finite, nearest binder first.** Actual `List Ty` lookup reflects the
  existing `Spine.BoundContext.prefix Γ Spine.EmptyContext` and agrees
  with literal one-binder push and arbitrary finite stack extension.
  Global free names remain typed pairs, not bound lookup entries.
  Unused entries outside K are allowed; the published finite window is
  a restriction on literal syntax/support and retained declarations.
- **Actual typed terms, bases, extras.** The mutually structural
  checker tests a bound occurrence using the original `C i = some σ`,
  enters lambda with the actual push, keeps ordinary and numbered base
  annotations equal to the head's complete *original* argument
  declaration, and checks every ordered extra in the same context.
  AuxApp remains distinct from the literal ordinary Head.app constructor
  and pays its function and argument types. The result-type test reflects
  actual `NTerm.type` and actual `Typed`; there is no all-source-subterm
  restriction or requirement of a closed ordinary term.
- **Actual fixed window.** `windowBit` checks the whole exact typed
  judgment, every type in existing `support`, and every head via
  packet442's exact original declaration-retaining `headBit`.
  Its target is exactly `InWindow S K C τ Q`, not a new predicate
  calibrated to the bit; no need to assume subtype-closed K to test
  membership. C-parametric correctness is a theorem about the modeled
  lookup parameter and does not claim arbitrary functions effectively
  encoded. `finiteWindowBit` has concrete finite list input and claims
  equivalence to the original finite binder context interpretation.

All existing syntax, typing, guard and head bit declarations are unchanged.
