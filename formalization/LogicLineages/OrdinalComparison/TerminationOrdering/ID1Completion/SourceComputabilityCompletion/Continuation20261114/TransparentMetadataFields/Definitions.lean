module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
def choose (target : Bool) (k : Nat) (yes no : Program 3) : Program 3 :=
  InternalAcceptance.branch (sameOf (leftOf (TransparentChildFields.rawCode target)) (constant 3 k)) no yes
def payload (target : Bool) : Program 3 := rightOf (TransparentChildFields.rawCode target)
def annotationRaw (target : Bool) : Program 3 :=
  choose target 1 (leftOf (payload target))
    (choose target 2 (leftOf (payload target))
      (choose target 3 (payload target)
        (choose target 5 (leftOf (rightOf (rightOf (payload target))))
          (choose target 7 (leftOf (payload target)) (constant 3 0)))))
def headRaw (target : Bool) : Program 3 :=
  choose target 4 (leftOf (payload target))
    (choose target 5 (leftOf (rightOf (payload target))) (constant 3 0))
def labelRaw (target : Bool) : Program 3 := choose target 5 (leftOf (payload target)) (constant 3 0)
def typesRaw (target : Bool) : Program 3 :=
  choose target 5 (leftOf (rightOf (rightOf (rightOf (rightOf (payload target)))))) (constant 3 0)
def guarded (V q : Program 3) : Program 3 := InternalAcceptance.branch V (constant 3 0) q
def annotation (V : Program 3) (target : Bool) : Program 3 := guarded V (annotationRaw target)
def head (V : Program 3) (target : Bool) : Program 3 := guarded V (headRaw target)
def label (V : Program 3) (target : Bool) : Program 3 := guarded V (labelRaw target)
def types (V : Program 3) (target : Bool) : Program 3 := guarded V (typesRaw target)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields
