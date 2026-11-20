# Actual atomic accessibility on the refined original checker

New target packet only, not a proof. Paper16 ordinals.tex 112–127.
The previous native #653 numeric and #656 object packets selected
exactly `refined i r`, same i/j/d, same supplied tape [x,w,y]. This
stage uses, and does not repropose or edit, that actual AST.

## Atomic I root (two exact targets)

* `ExactRefinedAtomicSuccessors`: known literal arithmetic equality to
  a bottom/free address at arbitrary open terms x,c,t,n, in the
  **actual new body** `sourceBody (data i j (refined i r) d) context`.
  Prove exactly the original universal successors formula for that
  same x (simple successor utility, not a new predicate). Its bound y
  is a fresh object variable with the original source x relabelled.
  Under the actual edge hypothesis use the existing checked
  `InternalComputabilityDownwardProof.edgeCases`: it opens the
  original `edgeExists` to the original supplied certificate and
  provides the hypothesis context through a real renaming map.
  Transport the *syntax* of the known atom equation across these
  exact binders, never across a changed body. For bottom, #656
  certificate gives object falsum and thus the consequent.
  For free, the actual certificate of that same y gives arithmetic
  equality to `packedBottomTerm c t` AND its original scalar carrier.
  Apply the bottom introduction at y directly, not at a replaced
  term or at a newly selected witness. The free successor premise does
  not need a scalar assumption on x, only the known shape.
* `ExactRefinedAtomicMembership`: from explicit original carrier on
  x and previous universal successors, use literal original
  accessibility introduction. In reverse, use literal original carrier
  extraction. No caller-provided Rules or extra object oracle;
  generic existing syntax/derivation suppliers apply to the actual
  new Data uniformly. Equality alone does not imply a carrier. Retain
  formula `membership false x` (actual I slice), not an external
  accessibility result or general C.

## Same selected tuple root (three exact targets)

* `ExactRefinedPresentationAndRules`: given actual original all-four
  Evaluates, #653 supplies the new exact original evaluation with
  only r changed. `exact_InterpretsEvaluatingPrograms` now applies
  to the new actual data. Instantiate the five original inference
  rules at that data anew using generic `InternalAccessibilityRulesProof`,
  not any correspondence by numerical equality of old/new bodies.
* `ExactReinstallSameRefinedTuple`: `TupleAt` is the complete #644
  originally selected packet at specified physical i,j,r,d,v,
  including all original scalar, direct and chosen p/a/h all-raw
  calibrations, UniqueResult, InputGuards, TypedProbeTotal, OpenLiteralParsed
  and AlignedCarriersAt. Reinstall for identical i,j,d,v,W and actual
  `refined i r`, no reproving of arithmetic by reflection. The
  InputGuards field quantifies all bodies, so instantiate its old
  proof at the actual new body and use **syntactic identity only**
  of the two scalar carrier formulas (their definition mentions i
  only). Actual arbitrary-Data TypedProbeTotal comes from the specific
  #641 supplier at new d′ with original ChildClosed derived from
  ValidWindow. Actual #644 alignment is applied directly at new
  d′ with these newly installed hypotheses, hence same supplied u.
* `ExactReinstallConcreteRefinedTuple`: choose old concrete packet
  by actual accepted #644 then return both packets at the exact same
  original leaves. Original ValidWindow remains explicit: no claim
  of the resource-stopped mixed original fixed-S,K target.

Keep two separate target preflights, frozen before proof. Later and
not encoded here: given-u base-ground fresh C via the genuine
three-slot `shapeAt` from #631 and original aligned scalar from
reinstalled #644. Its closure will require physical block elimination,
not an assumption shape exists outside the object calculus. This
packet does not assert higher arrow C, neutral applications, fresh
variable computability across all types, reinstalled ForwardRule/
pullback, or any numbered termination/BH promotion.
