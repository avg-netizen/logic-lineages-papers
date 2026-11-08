module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFold
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The SAME four binary leaves selected before every source window and
ambient context. No semantic, invariant or congruence field is added. -/
abbrev Data := InternalOriginalUniformDescentSelection.Data

abbrev validity (data : Data) : Program 2 :=
  InternalOriginalUniformDescentSelection.validity data

/-- The whole original parent, both original children, and its original
codomain are inspected at one unchanged parameter. The separate tag-two
test remains in openGuardP; this guard is not asserted equal to V. -/
def rootGuard (data : Data) : Program 2 :=
  InternalAcceptance.conjunction (validity data)
    (InternalAcceptance.conjunction
      (InternalParameterizedApplicationResultStack.wireP (validity data)
        (fun _ : Fin 1 => InternalCanonicalResultFoldOpening.functionChild))
      (InternalAcceptance.conjunction
        (InternalParameterizedApplicationResultStack.wireP (validity data)
          (fun _ : Fin 1 => InternalCanonicalResultFoldOpening.argumentChild))
        (InternalParameterizedApplicationResultStack.wireP data.member
          (fun _ : Fin 1 => InternalCanonicalResultFoldOpening.rootCodomain))))

def leaf (data : Data) : Program 2 :=
  InternalOriginalUniformDescentSelection.representative data

/-- Inputs [domain,codomain,functionOutput,argumentOutput,parameter]. The
raw application uses the whole child outputs, with no codomain repacking. -/
def rawApplicationAt : Program 5 :=
  .composition application ![.projection 0,.projection 1,.projection 2,.projection 3]

def combine (data : Data) : Program 5 :=
  .composition (leaf data) ![rawApplicationAt,.projection 4]

/-- The already checked stack machine and its ORIGINAL 2*payload+1 fuel.
The parameter is outside the state and is never a termination measure. -/
def foldN (data : Data) : Program 2 :=
  InternalParameterizedApplicationResultStack.foldP (rootGuard data) (leaf data) (combine data)

def goodRunH (data : Data) : Program 2 :=
  InternalParameterizedApplicationResultFoldCalibration.goodRunP
    (rootGuard data) (leaf data) (combine data)

def sourcePremises {α : Type} (data : Data)
    (input typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (validity data) InternalOriginalStepGuard.one input parameter ⊓
    graph1 InternalUnpair.left typ input

def foldGraph {α : Type} (data : Data)
    (out input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (foldN data) out input parameter

def goodRunAccepted {α : Type} (data : Data)
    (input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (goodRunH data) InternalOriginalStepGuard.one input parameter

def certifiedResult {α : Type} (data : Data)
    (out input parameter : OrdinaryArithmetic.Term α) : Formula α :=
  InternalParameterizedApplicationCertifiedResultFoldClosure.certifiedFoldP
    (rootGuard data) (leaf data) (combine data) out input parameter

/-- The actual source V, original raw left field and the SAME T(out,p)=out.
This is not N-, R-, D- or B-fixedness. -/
def outputInvariant {α : Type} (data : Data)
    (out typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  InternalOriginalUniformDescentSelection.outputInvariant
    data.oldRepresentative (validity data) out typ parameter

def certifiedOutput {α : Type} (data : Data)
    (out input typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  certifiedResult data out input parameter ⊓ outputInvariant data out typ parameter

/-- The output is bound internally; input, requested type and parameter
are all transported under the original object-language existential. -/
def hasCertifiedOutput {α : Type} (data : Data)
    (input typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  existsOne (certifiedOutput data (.var (.inr 0))
    (input.relabel Sum.inl) (typ.relabel Sum.inl) (parameter.relabel Sum.inl))

def successfulOutput {α : Type} (data : Data)
    (out input typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  goodRunAccepted data input parameter ⊓ outputInvariant data out typ parameter

def typedOutput {α : Type} (data : Data)
    (out input typ parameter : OrdinaryArithmetic.Term α) : Formula α :=
  goodRunAccepted data input parameter ⊓
    InternalOriginalUniformDescentSelection.typedAccepted
      data.oldRepresentative (validity data) data.member out typ parameter

/-- Input, type and parameter all vary INSIDE the strong-payload predicate.
The only size premise is the original right-field graph of that input. -/
def payloadMatrix {α : Type} (data : Data) (payload : OrdinaryArithmetic.Term α) :
    Formula (α ⊕ Fin 3) :=
  let input : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 1)
  let parameter : OrdinaryArithmetic.Term (α ⊕ Fin 3) := .var (.inr 2)
  (graph1 InternalUnpair.right (payload.relabel Sum.inl) input).imp
    ((sourcePremises data input typ parameter).imp
      (hasCertifiedOutput data input typ parameter))

def atPayload {α : Type} (data : Data) (payload : OrdinaryArithmetic.Term α) : Formula α :=
  InternalClosedPrograms.allBlock (payloadMatrix data payload)

/-- Inputs [domain,codomain,canonicalFunction,RAWargument,parameter]. Only
the raw argument is normalized before the SAME combine; the function is
not fed through N a second time. -/
def actualJ (data : Data) : Program 5 :=
  .composition (combine data)
    ![.projection 0,.projection 1,.projection 2,
      .composition (foldN data) ![.projection 3,.projection 4],.projection 4]

def applicationGraph {α : Type} (data : Data)
    (out d e x a parameter : OrdinaryArithmetic.Term α) : Formula α :=
  programGraph (actualJ data) out ![d,e,x,a,parameter]

/-- Original constructors, the actual child source/type graphs, explicit
member(codomain,p), N(function,p)=x and actualJ. Parent validity, opening,
successful child runs, fixed argument and congruence are conclusions. -/
def representativePremises {α : Type} (data : Data)
    (arrow d e fn arg parent x out parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 InternalListCodec.consCode arrow d e ⊓
    (graph2 (validity data) InternalOriginalStepGuard.one fn parameter ⊓
      (graph1 InternalUnpair.left arrow fn ⊓
        (graph2 (validity data) InternalOriginalStepGuard.one arg parameter ⊓
          (graph1 InternalUnpair.left d arg ⊓
            (graph2 data.member InternalOriginalStepGuard.one e parameter ⊓
              (foldGraph data x fn parameter ⊓
                (graph4 application parent d e fn arg ⊓
                  applicationGraph data out d e x arg parameter)))))))

def representativeConclusion {α : Type} (data : Data)
    (parent out e parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (validity data) InternalOriginalStepGuard.one parent parameter ⊓
    certifiedOutput data out parent e parameter

/-- Laws of this concrete selection to be proved without calibration or
stored correctness fields. Every internal parameter stays symbolic. -/
def InternalLaws (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α)),
  (∀ out input typ parameter : OrdinaryArithmetic.Term α,
    Nonempty (Derivation body Gamma
      ((sourcePremises data input typ parameter).imp
        ((foldGraph data out input parameter).imp
          (successfulOutput data out input typ parameter))))) ∧
  (∀ input typ parameter : OrdinaryArithmetic.Term α,
    Nonempty (Derivation body Gamma
      ((sourcePremises data input typ parameter).imp
        (hasCertifiedOutput data input typ parameter)))) ∧
  (∀ out input typ parameter : OrdinaryArithmetic.Term α,
    Nonempty (Derivation body Gamma
      ((sourcePremises data input typ parameter).imp
        ((graph2 data.member InternalOriginalStepGuard.one typ parameter).imp
          ((foldGraph data out input parameter).imp
            (typedOutput data out input typ parameter)))))) ∧
  (∀ arrow d e fn arg parent x out parameter : OrdinaryArithmetic.Term α,
    Nonempty (Derivation body Gamma
      ((representativePremises data arrow d e fn arg parent x out parameter).imp
        (representativeConclusion data parent out e parameter))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFold
