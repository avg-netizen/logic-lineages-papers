module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPut
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- NEW evaluator-key construction. It is NOT the earlier ObservedPut.refined.
The calibrated representative stays a least packed code; E is only a class-test key. -/
def prepared := SixSol20261113.Erasure.ObservedPut.prepared
def baseRepresentative (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Program 2 :=
 (prepared p H G W).base.oldRepresentative
def evaluatorKey (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Program 2 :=
 OriginalHereditaryEvaluatorDefinitions.evaluator (baseRepresentative p H G W)
def member (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Program 2 :=
 InternalOriginalUniformContextMembership.contextMember (prepared p H G W).base.member
/-- Candidate domain is literal, including original target/source/window.
No native decoder or relation oracle is embedded in this AST. -/
def kernel (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Program 3 :=
 InternalAcceptance.conjunction
   (.composition (OriginalActiveClassKernel.domainProgram (prepared p H G W) H G W)
     ![.projection 1,.projection 2])
   (OriginalActiveClassKernel.keyTest (evaluatorKey p H G W))
/-- Preserve original P on all inactive seeds, including malformed vectors. -/
def classTest (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) : Program 3 :=
 InternalAcceptance.branch
   (.composition (OriginalActiveObservedClass.activation (prepared p H G W) H G W)
     ![.projection 0,.projection 2]) P (kernel p H G W)
def minimumInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :=
 OriginalTransparentMinimum.minimumInputs H G (classTest p H G W P) (prepared p H G W)
def refined (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :=
 OriginalFinalGuardedRank.refined (minimumInputs p H G W P) H G W
def finalInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :=
 OriginalLambdaTraversalSelection.finalInputs (refined p H G W P)
def finalData (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :=
 OriginalLambdaTraversalSelection.finalData (refined p H G W P)
def relationTest (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :=
 OriginalTransparentMinimum.reflexiveClassTest (OriginalTypedDecoder.target H G) (classTest p H G W P)
def Domain {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input parameter : OTerm alpha) : Formula alpha :=
 OriginalActiveClassKernel.Domain (prepared p H G W) H G W input parameter
def Same {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (left right parameter : OTerm alpha) : Formula alpha :=
 SixSol20261113.Erasure.EvaluatorErasureDefinitions.SameEvaluator (baseRepresentative p H G W) left right parameter

def Fields {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3)
    (s t cert parameter typ raw head base label : OTerm alpha) : Formula alpha :=
  graph2 (InternalOriginalUniformDescentSelection.validity (finalData p H G W P))
      (numeral 1) s parameter ⊓
    (graph2 InternalPairing.pairing s typ raw ⊓
      (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base ⊓
        (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label ⊓
          graph2 SixSol20261112.Erasure.PutRoot.certificateCode cert s label)))


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPut
