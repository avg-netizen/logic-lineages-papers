# L3 frozen source correspondence

Selected unpaid bridge: acceptance of the actual mixed recognizer recovers
the original root source and SAME leaf edge, without assuming those two graphs.
The existing `ActualClosedRestrictedTransport` explicitly assumes both graphs
beside recognition. The latest `RecognizesFactor` transfers recognition from
the explicit closed checker to its underlying leaf but does not recover the
root graphs. These are read in their real source files before target selection.

`Erasure/Targets.lean` freezes two contracts before proof authorship:

1. `RecognizerRootSoundness` quantifies over the original arbitrary source,
   leaf, proof context and all four runtime terms; it recovers both original
   root graphs internally from the actual recognizer alone.
2. `ClosedRecognizedErasure` composes this with the checked closed-recognizer
   factor and restricted trace transport. Its sole trace premise is acceptance
   by the actual closed-checker recognizer; source validity and underlying
   leaf acceptance become proved intermediate conclusions. Actual insertion,
   same outer parameter, original endpoints and exact raw erasures persist.

Source relation, certificate encoding and runtime transitions are unchanged.
This is a constructive supplier toward paper06 `lem:id1`; arbitrary original
unrecognized source rules, selected final-tuple correspondence, full erasure
transformer and internal I/C/accessibility remain pending. Native calibration
is not an internal derivation. No canonical endpoint premise is introduced.

Root is sole native compiler. Candidate proofs are unaccepted until focused
exact-type and standard-axiom gates pass with source-matched receipts.
