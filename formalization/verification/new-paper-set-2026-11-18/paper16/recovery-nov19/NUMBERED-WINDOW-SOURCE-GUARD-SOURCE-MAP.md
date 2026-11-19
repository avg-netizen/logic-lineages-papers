# Original symbolic block guard, supporting only

The full tuple proof consumes original binders one by one numerically
but must still recognize the actual symbolic block result and retain
the same symbolic signature, genuine outside binder stack and original
declaration-retaining type support. `NumberedWindowSourceGuardTargets`
proposes three exact supporting comparators; it does not assert
arbitrary derivation locality or a full numerical path.

- `ActualBlockGuard`: substitute the actual nearest-binder-first block
  `values` using unchanged `Spine.substitute values 0 q`; original q is
  typed under precisely the declared prefix plus its actual outside
  context. Return the same type, original validity and declaration-
  retaining admissibility in that outside context.
- `ActualBaseBlockGuard`: preserve every original base item's positional
  type in the literal `substituteArgs` result, with validity and the same
  window. No currying, changed owner declaration, or nonempty restriction.
- `ActualExtrasBlockGuard`: keep the exact actual typed extra list's
  order and whatever individual types its elements already carry. No
  base arity or common extra type is added.

The claims take arbitrary outside contexts and arbitrary valid typed
block images, including higher types, marks and globally typed free
names. No `EmptyContext` specialization, designated initial source,
fixed finite free-name inventory, port, or observed-target premise is
added. In proof, the old general `DecisionSourceSubstitutionProof`
supports a scoped projection by choosing finite name/head lists from
the actual q, base or extras, and actual images. No premise about those
chosen lists remains in the exact contracts. Existing
`SpineSubstitutionProof.finiteCompatible` pays the actual typed binder
compatibility, rather than assuming an arbitrary substitution law.
