module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeaf
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original raw packed variable tag: left(right(source)) = 0. This is a
literal total Program, not a parser or a claim that every such raw code is
well typed. Accepted original leaf certificates pay that separate fact. -/
def variableTest : Program 1 :=
  InternalApplicationStepPeel.same
    (InternalApplicationStepPeel.constructorTag (.projection 0))
    (InternalAcceptance.constantZero 1)

/-- Inputs remain [source,target,originalStepCertificate,parameter]. -/
def variableAt : Program 4 :=
  .composition variableTest (fun _ : Fin 1 => .projection 0)

/-- The existing exact bottom constructor uses BOTH original outer-type
occurrences, producing pair(typeCode,pair(3,typeCode)). -/
def expectedBottom : Program 4 :=
  .composition BottomRepresentative.bottomCode
    (fun _ : Fin 1 => leftOf (.projection 0))

/-- Exact-one implication: a variable source requires the actual target to
be its same-type bottom. All non-one tests take the accepting zero branch.
The normalization pays arbitrary symbolic values internally. -/
def variableGuard : Program 4 :=
  InternalAcceptance.branch
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize variableAt)
    (InternalLessThan.constantOne 4)
    (InternalApplicationStepPeel.same (.projection 1) expectedBottom)

/-- The original leaf is retained as a factor. Added guards must be proved
redundant on ALL raw inputs, including malformed/rejected cases. No source,
target, parameter, or original StepCertificate is changed or reencoded. -/
def refined (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.conjunction oldStep
    (InternalAcceptance.conjunction
      (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest) variableGuard)

abbrev accepted {α : Type} (leaf : Program 4)
    (rawSource target certificate parameter : OTerm α) : Formula α :=
  graph4 leaf InternalOriginalStepGuard.one rawSource target certificate parameter

/-- The old acceptance factor is a literal internal graph consequence,
without assuming native calibration or consistency of Delta. -/
def OriginalFactor (oldStep leaf : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (rawSource target certificate parameter : OTerm α),
  Nonempty (Derivation body Delta
    ((accepted leaf rawSource target certificate parameter).imp
      (accepted oldStep rawSource target certificate parameter)))

/-- Only raw ROOT constructor laws. The variable antecedent supplies the
actual tag-test and outer-type graphs. The conclusion uses the existing
literal bottomCode graph. Bottom rejection uses the exact bottomTest,
including equality of its outer and inner type occurrences. No native
source parse, Gamma, source relation, or semantic fact is an inference rule. -/
def ConstructorCases (leaf : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (rawSource target certificate parameter typeCode : OTerm α),
  Nonempty (Derivation body Delta
    ((accepted leaf rawSource target certificate parameter ⊓
      (graph1 variableTest InternalOriginalStepGuard.one rawSource ⊓
        graph1 InternalUnpair.left typeCode rawSource)).imp
      (graph1 BottomRepresentative.bottomCode target typeCode))) ∧
  Nonempty (Derivation body Delta
    ((graph1 BottomRepresentative.bottomTest InternalOriginalStepGuard.one rawSource).imp
      (accepted leaf rawSource target certificate parameter).not))

/-- Only the oldStep AST changes. Every other globally selected input,
including source fallback, computability, window, and lift inputs, is literal. -/
def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with oldStep := refined p.oldStep }

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeaf
