# Paper 16: same-body actual output/shape-guarded selected tuple

This supports the same original typed probe component of (T)
(`16-persistent-marking-termination-ordering/sections/ordinals.tex:113–127`).
The separate fixed-source numerical output-carrier proof is not imported
or treated as passed. `OutputScalarLaw s i` is an explicit true all-input
premise of the specialization to a given s and actual program i.

The exact current `Inputs` record retains old physical priorTyped,
optionApplication, scalarProg and freshBound, but changes the
application guard to literal `outputGuard i (refinedApplication p)`.
The old chosenA is definitionally the same, to which the new exact theorem
testifies. The actual h is newly `chosenH newInputs W`; no old typed
totality, shape, calibration or alignment is transplanted to it.

- The numerical proof first uses the original shape-refinement calibration
  on the existing literal checker, then the actual output conjunction
  calibration under the supplied law. It never uses admissibility of
  arbitrary Settings or a numerical/unrestricted object reflection.
- Genuine open output projection and then shape forget lift existing
  uniqueness and both input carrier guards to the new checker. They do
  not imply old-acceptance→new-acceptance at arbitrary open tapes.
- The original parsed typed assembly is rerun on the new Inputs and
  genuine ValidWindow. Same-body (i,j,r,d), numerical Evaluates, original
  Interprets and Rules are not changed. New typed/calibration/literal
  and alignment theorems all mention the new physical graph.

`exact_ApplicationOutputGuardReinstall` starts from BaseAt;
`exact_ApplicationOutputGuardReselect` accepts an already held original
TupleAt and independently reselects. Neither produces ForwardRule or
transports h-dependent derivations; neither invokes an unrestricted
fixed-settings closure theorem.

Exact serial root: `NumberedWindowInternalApplicationOutputGuardReinstallProof`
(target dependency 877 local / 29 external, proof 1797 / 33).
Its only static high-profile import is Mathlib.Tactic.Linarith, on the
identical previously used typed-calibration chain as
`NumberedWindowInternalAtomicApplicationShapeReinstallProof`
(via GorbowRegistryTupleProof); the pinned .olean is present at drafting.
No Hydra, Sym2, GameAdd or Rank in static reachable imports.

Exact source and existing premise pins (SHA256):
~~~text
ea4dddeb72363f475fe3b2f9c8f31aa0296dbeb17f833ee67ad58ddf276c916c  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalApplicationOutputGuardReinstallTargets.lean
e9ab46ffb99b8fb210961721c3b86eeb82cff7c5a7fa0214b334785d70ae13e6  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalApplicationOutputGuardReinstallProof.lean
91305f64c073c238319367b51c8cb6cfd4a05f5f393d9174baa49f2ad250f9c0  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalApplicationOutputGuardNumericProof.lean
27d48c026115a4d9275818e9a5e380ea35a107381bbc5dc3d9e27f2ce11467dc  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalApplicationOutputGuardOpenProof.lean
08927d5dc951c261a40307e4eed22ed3658b379cd6455e9bf807769b50d93612  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalAtomicApplicationShapeReinstallProof.lean
0ad6d2309b696874ce045843df11eaa546ce9a94be23cfeaf678d6282f1f6d06  formalization/LogicLineages/PersistentMarking/NumberedWindowInternalFreshProbeParsedTypedDefinitions.lean
526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5  16-persistent-marking-termination-ordering/sections/ordinals.tex
~~~
