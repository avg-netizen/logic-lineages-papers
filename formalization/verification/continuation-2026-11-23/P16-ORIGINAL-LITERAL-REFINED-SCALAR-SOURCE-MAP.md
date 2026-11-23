# Paper 16: exact atomic I in the same literal-count body

Source freeze, pending native. The new state is explicitly
`refinedLiteral i r = literalData i (refined i r)
 = data i (jRaw i) (refined i r) (dCore i (refined i r) permutation)`.
This is not the old #571/#660 physical body, nor a claim that the opaque
arbitrary even `r` exposes the refinement's branches.

* `InstallProof.exact_ReinstallLiteralRefinedScalar` uses #653's exact
  original all-input numeric positive calibration on the same old scalar
  and original positive fits, yielding the real specific refined r.
  Checked chosen literal `CountFit` and fresh typed list/direct reinstallation
  give `Evaluates` / `Interprets` / actual original (A) rules for the above
  same new body. The dCore call uses the **same** physically selected refined
  r used in the body's even edge. No assumed guard, body equivalence, proof
  transport from an older body, or CountFit existence remains.
* `AtomicProof.exact_TypedRefinedLiteralAtomicI` takes actual original
  scalar output one and exact symbolic packed bottom or packed free shape
  in that **same** body. Original even carrier coordinates and arbitrary-j,d
  #659 specialize with *exact* jRaw and physical dCore, giving actual I at
  arbitrary open q. No host-side numerical reflection, no assumed typing
  from shape, no type-indexed higher C for arbitrary arrows, no extension
  beyond those two actually paid packed shapes.

## Printed proof boundary

Paper 16 `sections/ordinals.tex:149–153` (I→singleton J and finite union) is
a same-body conditional bridge, not a proof of arbitrary I. The remaining
independent actual `CertifiedOriginSplit` is still required for that J route.
Even with it, before universal scalar I of lines 183–187 one still needs:

1. A same-body choice of genuine typed/application/fresh observation and
   direct positive path suppliers for the typed C rules (lines 100–140).
   The object typed-C→I proof #611 requires actual typed-probe totality,
   computable fresh variables, and accessibility pullback; it cannot be fed
   mere numeric equality or admitted-source meta facts. Some existing
   neutral/variable packages use distinct older built tuples. A lambda still
   needs the same actual instantiated beta/positive-path-or-equality and
   lower body facts at the correct typed context.
2. The four nested **object** inductions (L), lines 155–181, genuinely
   quantify each later coordinate after the earlier one changes: finite
   head class, J(base), finite label then ω, J(extras), and output type and
   typed extras. Need actual base/extra changes assembled using the new
   literal J and selected raw successors, and actual head/reset/Select/
   Copy/multiset/abstraction/beta consequences. Meta-level
   `NumberedWindowConstructorComputabilityProof.owners` is not this proof.
3. The final structural induction under a real computable substitution
   (`NumberedWindowStructuralComputabilityProof.substitution` is external,
   not ID₁); its actual typed body/program witnesses must land in that
   installed typed C and then I. Arbitrary stage interpretation or old-body
   transport are not consequences of the new choice.

The small packet only pays the typed packed bottom/free leaves on this
same even/odd body. No universal I/C, full arithmetic accessibility,
certified origin split, or printed theorem promotion.

| New `NumberedWindowInternalLiteralRefinedScalar…` leaf | SHA-256 | Local/external closure |
|---|---|---|
| `Targets` | `bf2a8358d1d1314cde759fcffe5ff348c255876afb569dd1d851d5cd9d755a7a` | 1273/32 |
| `InstallProof` | `e33bc2ca05d3958aac820db60606c437d1a4fcea64bc7d1f1e3fe8a03f0cf174` | 1354/33 |
| `AtomicProof` | `f465795a4f27cdd48a2e0d4b576dba25bb33bd09d577abd0e527091b6d3f1fe2` | 1324/32 |

No Hydra/GameAdd/Sym2/Linarith in recursive source scans. Separately gate
`InstallProof.exact_ReinstallLiteralRefinedScalar` and
`AtomicProof.exact_TypedRefinedLiteralAtomicI`.
Unchanged suppliers `AtomicRefinementNumericChecks`
`3d401788e761e65b5a269ebd5d7e945b208739fd0597c370a08783fafaa640cf`
and `AtomicMembershipChecks`
`978f13da60e22bdd394745b3b55a7d8796bb63ba615e88b9277a370c33749b62`.
