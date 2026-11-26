module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottom
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The SAME original nil-path/direct-bottom certificate constructor already
checked for variables. No new certificate encoding or completeness choice. -/
abbrev certificateCode : Program 1 := OriginalTransparentVariableStep.certificateCode

def active : Program 4 :=
  InternalApplicationStepPeel.same (.projection 2)
    (.composition certificateCode (fun _ : Fin 1 => .projection 0))

/-- Original source validity, actual nonbottom test, and literal same-type
bottom target. No semantic predicate or oldStep acceptance enters this branch. -/
def acceptedValue (source : Program 2) : Program 4 :=
  InternalAcceptance.conjunction (OriginalTransparentVariableStep.sourceAt source)
    (InternalAcceptance.conjunction
      (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
      (InternalApplicationStepPeel.same (.projection 1) OriginalConstructorLeaf.expectedBottom))

def refined (source : Program 2) (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.branch active oldStep (acceptedValue source)

def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with oldStep := refined p.base.oldSource p.oldStep }

/-- Raw leaf premises. Abstract source acceptance is enough for this leaf,
NOT for the whole spine-guarded wrapper on arbitrary malformed tag-three codes. -/
def Premises {alpha : Type} (source : Program 2)
    (s t cert parameter typ : OTerm alpha) : Formula alpha :=
  graph2 source InternalOriginalStepGuard.one s parameter ⊓
    ((BottomRepresentative.bottomGraph InternalOriginalStepGuard.one s).not ⊓
      (graph1 InternalUnpair.left typ s ⊓
        (graph1 BottomRepresentative.bottomCode t typ ⊓ graph1 certificateCode cert s)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottom
