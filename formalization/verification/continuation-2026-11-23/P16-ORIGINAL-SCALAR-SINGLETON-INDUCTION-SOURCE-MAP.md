# Paper 16: literal original scalar induction for the packed singleton invariant

[ordinals.tex](../../../16-persistent-marking-termination-ordering/sections/ordinals.tex)
defines the one even/odd ID1 body at 84–98. At 149–153 the right next induction
is on the scalar Q, with odd membership on Q's actual packed singleton.

[New module](../../LogicLineages/PersistentMarking/NumberedWindowInternalScalarSingletonInductionProof.lean):
* The literal code of a singleton is `rawCons q 0`, using the actual raw
  field constructor already used by #1479 for its one singleton-bottom case.
  The source induction and its lower edges use the **even** actual scalar
  certificate relation. The target motive and its lower instances are actual
  **odd** membership of this specific code in the *same* tagged body.
* `exact_ActualScalarSingletonLowerInstance` is an object proof elimination:
  the lower hypothesis is universally quantified, and an actual scalar
  edge to the same successor is required before the actual singleton
  substitution. No external accessibility or coding surrogate is used.
* `exact_ActualScalarSingletonProgressiveInduction` takes the true open
  progress derivation under typed scalar carrier plus this strict-lower
  hypothesis, then performs the original internal slice induction. The
  progress derivation remains unpaid. In particular, the source has not
  reconstructed an arbitrary strict singleton certificate's actual
  descendants or proved an internal finite multiset fold; #1531's conditional
  binary union is a separate exact result with its own unproved prerequisites.
  This is not an unconditional singleton theorem, arbitrary multiset
  closure, or a numbered result.

Native author status: source only; the proof root expects two named axiom audits.
