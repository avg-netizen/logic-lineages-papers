module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryWorkBoundDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
/-- Jobs are pair(raw, pair(original window c, context code)). Raw list nodes
are intentionally not assigned a typed-term role by this operational packet. -/
def jobNumber {n : Nat} (c : Nat) (s : OriginalHereditaryWorkBound.State (Fin n)) : Nat :=
  Nat.pair (codeNumber s.code) (Nat.pair c (Encodable.encode s.context))
def consOf {n : Nat} (a b : Program n) : Program n :=
  .composition InternalListCodec.consCode ![a,b]
def firstParameter : Program 2 :=
  InternalAcceptance.branch (sameOf (leftOf (.projection 0)) (constant 2 1))
    (.projection 1)
    (pairOf (leftOf (.projection 1))
      (consOf (leftOf (rightOf (.projection 0))) (rightOf (.projection 1))))
def firstJob : Program 2 := pairOf (firstOf (.projection 0)) firstParameter
def secondJob : Program 2 := pairOf (secondOf (.projection 0)) (.projection 1)
/-- On malformed raw codes the existing literal arity/selectors still govern;
unknown tags are leaves, with no decoding or typedness assertion. -/
def childJobs : Program 2 :=
  InternalAcceptance.branch (sameOf (arityOf (.projection 0)) (constant 2 1))
    (InternalAcceptance.branch (sameOf (arityOf (.projection 0)) (constant 2 2))
      (constant 2 0) (consOf firstJob (consOf secondJob (constant 2 0))))
    (consOf firstJob (constant 2 0))
/-- An erased fake packed input is unpacked immediately; its artificial outer
zero is not a source type and is never fed to a source validity checker. -/
def unpackJob : Program 2 := pairOf (rightOf (.projection 0)) (.projection 1)
def deletionJobs : Program 2 :=
  .composition (OriginalHereditaryDeletionRows.rows unpackJob)
    ![pairOf (constant 2 0) (.projection 0),.projection 1]
def expansion : Program 2 :=
  .composition InternalApplicationValidityStackAppend.append ![childJobs,deletionJobs]
def childValues (raw parameter : Nat) : List Nat :=
  let fp := if tagValue raw = 1 then Nat.pair (Nat.unpair parameter).1
      (1 + Nat.pair (Nat.unpair (Nat.unpair raw).2).1 (Nat.unpair parameter).2)
    else parameter
  let first := Nat.pair (firstValue raw) fp
  if arityValue raw = 1 then [first]
  else if arityValue raw = 2 then [first,Nat.pair (secondValue raw) parameter] else []
def deletionValues (raw parameter : Nat) : List Nat :=
  OriginalHereditaryDeletionRows.values unpackJob
    (evaluate OriginalContextInsertion.length (List.Vector.ofFn ![(Nat.unpair parameter).2]))
    (Nat.pair 0 raw) parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansion
