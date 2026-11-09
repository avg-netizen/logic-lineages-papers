module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationTypingDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Application
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The source function and RAW argument are typed. Target function typedness
is derived from the same original edge. ActualJ normalizes only its argument;
neither supplied function nor argument is assumed fixed by the result fold. -/
def corePremises {α : Type} (data : Data) (oldStep : Program 4) (sigma tau : Ty)
    (x y a certificate out other parameter : OTerm α) : Formula α :=
  typedAccepted data x (numeral (typeNumber (.arrow sigma tau))) parameter ⊓
    (typedAccepted data a (numeral (typeNumber sigma)) parameter ⊓
      (edgeAccepted data oldStep x y certificate parameter ⊓
        (InternalParameterizedCanonicalResultFold.applicationGraph data out
          (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x a parameter ⊓
          InternalParameterizedCanonicalResultFold.applicationGraph data other
            (numeral (typeNumber sigma)) (numeral (typeNumber tau)) y a parameter)))

/-- One original pair graph, with a SYMBOLIC runtime Gamma coordinate. The
same parameter is passed to every original leaf and checker call. -/
def parameterPremises {α : Type} (context : Nat) (data : Data) (oldStep : Program 4)
    (sigma tau : Ty) (x y a certificate out other parameter gammaCode : OTerm α) : Formula α :=
  InternalOriginalUniformApplicationTyping.parameterGraph context parameter gammaCode ⊓
    corePremises data oldStep sigma tau x y a certificate out other parameter

/-- Reuse the original actual certificate constructors verbatim. The
parameter is never inserted into a certificate, and the argument remains RAW. -/
abbrev constructorWitnesses {α : Type} (sigma tau : Ty)
    (a certificate s t k sourceApp targetApp liftedStep lifted : OTerm α) : Formula α :=
  InternalCanonicalQuotientEdgeApplicationLift.constructorWitnesses sigma tau
    a certificate s t k sourceApp targetApp liftedStep lifted

/-- The only supplied lift output is the original edgeLift graph. Raw
selectors and application/step constructor witnesses are internal conclusions. -/
def liftPremises {α : Type} (context : Nat) (data : Data) (oldStep : Program 4)
    (sigma tau : Ty) (x y a certificate out other lifted parameter gammaCode : OTerm α) : Formula α :=
  parameterPremises context data oldStep sigma tau x y a certificate out other parameter gammaCode ⊓
    graph4 edgeLift lifted (numeral (typeNumber sigma)) (numeral (typeNumber tau)) a certificate

def typedOutputs {α : Type} (data : Data) (tau : Ty)
    (out other parameter : OTerm α) : Formula α :=
  typedAccepted data out (numeral (typeNumber tau)) parameter ⊓
    typedAccepted data other (numeral (typeNumber tau)) parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.Application
