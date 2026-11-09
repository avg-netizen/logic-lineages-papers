module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ComputabilityLeastDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObject
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open InternalComputabilityApplication InternalAccessibilityRules
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A read-only test of the ORIGINAL Object's raw right payload. This is
not installed in any selected Data, source, computability or lift Program. -/
def variableObjectTest : Program 1 :=
  .composition OriginalConstructorLeaf.variableTest (fun _ : Fin 1 => InternalUnpair.right)

abbrev variableObject {α : Type} (object : OTerm α) : Formula α :=
  graph1 variableObjectTest InternalOriginalStepGuard.one object

/-- Bind the ORIGINAL raw Gamma coordinate internally. The successor is
the literal original bottom Object of the SAME requested type and Gamma.
No Gamma decoder, re-encoding equation or supplied coordinate witness occurs. -/
def bottomAtSourceGamma {α : Type} (tau : Ty) (source target : OTerm α) : Formula α :=
  existsOne
    (graph1 InternalUnpair.left (.var (.inr 0)) (source.relabel Sum.inl) ⊓
      ComputabilityLeast.bottomGraph (target.relabel Sum.inl)
        (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) (.var (.inr 0)))

def VariableCertificateBottom (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) : Prop :=
  ∀ (tau : Ty) (α : Type) (Delta : List (Formula α)) (source target witness : OTerm α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
    ((typed comp tau (numeral context) source ⊓
      (variableObject source ⊓ certificate src false context source target witness)).imp
      (bottomAtSourceGamma tau source target)))

/-- Actual scalar I in the original combined-body calculus, at EVERY finite
type. Typedness and the literal Object variable test are the entire internal
antecedent; no type-window membership or successor/accessibility oracle. -/
def VariableLeast (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (context : Nat) : Prop :=
  ∀ (tau : Ty) (α : Type) (Delta : List (Formula α)) (object : OTerm α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
    ((typed comp tau (numeral context) object ⊓ variableObject object).imp
      (membership false object)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableObject
