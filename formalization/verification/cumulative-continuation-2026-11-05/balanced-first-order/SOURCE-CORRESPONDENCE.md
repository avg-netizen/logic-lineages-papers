# Balanced first-order source reduction

Paper08 `thm:balanced`, in `08-multivariate-collapse-comparison/paper.tex`, asserts
an effective BASE comparison formula with exactly the same variables, followed
by decidability of arbitrary Boolean/quantified combinations. This component
addresses the effective first-order source translation behind that second clause.
The unrestricted BASE solver and whole theorem remain pending.

Each atom retains its own original balanced shape, whole pair certificate, shared
basis and typed operands. Repeated/dependent basis entries and outside remainders
are not replaced by independent variables. Original raw support discards zero
outside multiples, as the source explicitly specifies before thm:balanced.

The source level-zero grammar uses positive raw variables. The accepted balanced
semantic supplier requires positivity only on each original pair support. This
translation consequently assumes positivity only on the whole formula's original
FREE names and uses explicitly positive existential binders. Bound-name positivity
is propagated by Function.update, including repeated names and shadowing; an old
bound value and unrelated coordinates remain unrestricted. Positive universality
is the ordinary negation/existential dual. There are no added per-atom positivity
guards that could change meaning under negation.

Every positive binder translates to a Nat binder with 0<x inside its scope. The
atom comparison formula and exact-support padding are reused literally. Targets
separate environment propagation, source truth, exact free-variable membership,
literal code calibration, interpreted output code, actual total numeric compilation,
and the universal positive domain. No quantifier elimination or decision procedure
is claimed. No new premise replaces the missing mathematical BASE supplier.
