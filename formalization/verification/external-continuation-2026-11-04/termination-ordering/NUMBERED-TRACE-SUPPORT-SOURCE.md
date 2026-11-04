# Trace support and arbitrary typed-renaming image closure

Draft for review; no proof/export. Actual primary/step trace consequences for paper 06 context reasoning.

The first three targets preserve arbitrary typed P forward through packed, typed and tuple traces at any count, including zero. Primary edges use accepted support iff, raw steps use one-way StepSupport, and composition threads support. The last three targets start at a literal renamed source and allow an arbitrary actual endpoint of the trace. The endpoint must be a literal renamed term/tuple of the same kind, using range support and the accepted image-existence iff.

Renaming rho is arbitrary and may be noninjective. The conclusions assert only existence of a preimage endpoint, NOT an old-context trace to it, injectivity or count reflection. No finite signature, subtype closure, universe or precedence condition is needed for these raw structural statements. The binder-aware support ensures Abs introduces only an allowed bound here and beta cannot introduce an external fresh variable; these cases were paid in StepSupport.

No weakening reflection, numeric quotient/Acc/C stability, ID1 or all-term result is asserted. Prior accepted bytes unchanged.
