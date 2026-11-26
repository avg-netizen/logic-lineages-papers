module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPath
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

abbrev bottomAccepted {α : Type} (input : OTerm α) : Formula α :=
  graph1 BottomRepresentative.bottomTest InternalOriginalStepGuard.one input

abbrev variableAccepted {α : Type} (input : OTerm α) : Formula α :=
  graph1 OriginalConstructorLeaf.variableTest InternalOriginalStepGuard.one input

/-- BOTH directions at the ACTUAL full canonical fold. The original window,
source validity, raw left/type and supplied fold graphs are the entire
antecedent. No native calibration, bottom-shape oracle, child-success record
or selected-representative invariant is assumed. -/
def FullFoldBottomPreservation (data : Data) (window : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (out input typeCode parameter : OTerm α),
  Nonempty (Derivation body Delta
    ((OriginalVariableRepresentative.windowGraph window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises data input typeCode parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph data out input parameter)).imp
      ((bottomAccepted out).iff (bottomAccepted input))))

/-- Original QUOTIENT endpoint laws, without supplied raw certificate
selectors, source validity, target typing or raw-source/endpoint equality.
The exact variable test and raw left/type graph determine the SAME literal
bottomCode with both original type occurrences. Exact bottom is terminal. -/
def QuotientConstructorCases (data : Data) (oldStep : Program 4) (window : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (x y certificate parameter typeCode : OTerm α),
  Nonempty (Derivation body Delta
    ((OriginalVariableRepresentative.windowGraph window x parameter ⊓
      (edgeAccepted data oldStep x y certificate parameter ⊓
        (variableAccepted x ⊓ graph1 InternalUnpair.left typeCode x))).imp
      (graph1 BottomRepresentative.bottomCode y typeCode))) ∧
  Nonempty (Derivation body Delta
    ((OriginalVariableRepresentative.windowGraph window x parameter ⊓ bottomAccepted x).imp
      (edgeAccepted data oldStep x y certificate parameter).not))

/-- ORIGINAL positive and reflexive path checkers at EVERY raw path code.
No cons/entry witnesses, parse-success, length or fuel premise is supplied.
Positive variable paths end at literal same-type bottom. Ordinary bottom
paths are identities; positive bottom paths are rejected. No path existence
or converse implication is asserted. -/
def PathConstructorCases (data : Data) (oldStep : Program 4) (window : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (x y pathCode parameter typeCode : OTerm α),
  Nonempty (Derivation body Delta
    ((OriginalVariableRepresentative.windowGraph window x parameter ⊓
      (variableAccepted x ⊓
        (graph1 InternalUnpair.left typeCode x ⊓
          InternalParameterizedPathChecker.positiveGraph (edgeChecker data oldStep)
            x y pathCode parameter))).imp
      (graph1 BottomRepresentative.bottomCode y typeCode))) ∧
  Nonempty (Derivation body Delta
    ((OriginalVariableRepresentative.windowGraph window x parameter ⊓
      (bottomAccepted x ⊓
        InternalParameterizedPathChecker.pathGraph (edgeChecker data oldStep)
          x y pathCode parameter)).imp
      (equal y x))) ∧
  Nonempty (Derivation body Delta
    ((OriginalVariableRepresentative.windowGraph window x parameter ⊓ bottomAccepted x).imp
      (InternalParameterizedPathChecker.positiveGraph (edgeChecker data oldStep)
        x y pathCode parameter).not))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableQuotientPath
