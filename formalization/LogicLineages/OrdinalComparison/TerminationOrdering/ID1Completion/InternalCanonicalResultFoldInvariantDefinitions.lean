module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariant
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- V is the EXACT recursive source checker. Both original leaves remain
arbitrary. This is the conjunction of the target validator at constantOne and
the universe validator at member, not an unconstrained unary predicate and
not the universe branch alone. No calibration or closure field is stored. -/
def validity (old : InternalOriginalStepGuard.Data) (member : Program 1) : Program 1 :=
  (InternalApplicationValidityStack.recursiveData old member).sourceValid

/-- Only actual input validity and its ORIGINAL raw left field are premises.
Requested-type membership is intentionally absent. -/
def sourcePremises {α : Type} (old : InternalOriginalStepGuard.Data) (member : Program 1)
    (input typ : OrdinaryArithmetic.Term α) : Formula α :=
  InternalBoundedDescentNormalizer.validGraph (validity old member) input ⊓
    InternalBoundedDescentNormalizer.leftGraph typ input

/-- Exact frozen opening aliases, with no altered guard, combine, fuel or
fallback. BOTH actual H(input)=1 and N(input)=out graphs are retained. -/
def certifiedResult {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input : OrdinaryArithmetic.Term α) : Formula α :=
  InternalApplicationCertifiedResultFoldClosure.certifiedFold
    (InternalCanonicalResultFoldOpening.rootGuard (validity old member) member)
    (InternalCanonicalResultFoldOpening.leaf representative (validity old member))
    (InternalCanonicalResultFoldOpening.combine representative (validity old member)) out input

/-- Output fixedness means T(out)=out for the checked descent transition.
It does not mean N-, D-, B- or R-fixed, nor is fixedness an input premise. -/
def outputInvariant {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out typ : OrdinaryArithmetic.Term α) : Formula α :=
  InternalBoundedDescentNormalizer.validGraph (validity old member) out ⊓
    (InternalBoundedDescentNormalizer.leftGraph typ out ⊓
      InternalBoundedDescentNormalizer.transitionGraph
        representative (validity old member) out out)

def certifiedOutput {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input typ : OrdinaryArithmetic.Term α) : Formula α :=
  certifiedResult old representative member out input ⊓
    outputInvariant old representative member out typ

/-- The output is bound by the ORIGINAL object-language existential. Both
original free terms are capture-avoidably relabeled under this one binder. -/
def hasCertifiedOutput {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (input typ : OrdinaryArithmetic.Term α) : Formula α :=
  existsOne (certifiedOutput old representative member (.var (.inr 0))
    (input.relabel Sum.inl) (typ.relabel Sum.inl))

/-- The actual unchanged fold N, not a successful-run premise or a new
relation whose graph is defined by the desired invariant. -/
def foldGraph {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input : OrdinaryArithmetic.Term α) : Formula α :=
  graph1 (InternalCanonicalResultFoldOpening.foldN representative (validity old member) member)
    out input

def goodRunAccepted {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (input : OrdinaryArithmetic.Term α) : Formula α :=
  graph1 (InternalCanonicalResultFoldOpening.goodRunH representative (validity old member) member)
    InternalOriginalStepGuard.one input

def successfulOutput {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input typ : OrdinaryArithmetic.Term α) : Formula α :=
  goodRunAccepted old representative member input ⊓
    outputInvariant old representative member out typ

/-- Existing canonical typed checker at the SAME R/V/member selection. Its
membership conjunct must be supplied separately in the typed-output target. -/
def typedOutput {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input typ : OrdinaryArithmetic.Term α) : Formula α :=
  goodRunAccepted old representative member input ⊓
    InternalCanonicalDescentSelection.typedAccepted
      representative (validity old member) member out typ

/-- At each induction payload quantify EVERY original packed input and
requested type, in that order. The payload graph connects that arbitrary
input to the bound; no packed-code or normalized-output size bound appears. -/
def payloadMatrix {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload : OrdinaryArithmetic.Term α) :
    Formula (α ⊕ Fin 2) :=
  let input : OrdinaryArithmetic.Term (α ⊕ Fin 2) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (α ⊕ Fin 2) := .var (.inr 1)
  (graph1 InternalUnpair.right (payload.relabel Sum.inl) input).imp
    ((sourcePremises old member input typ).imp
      (hasCertifiedOutput old representative member input typ))

/-- Original finite universal block, suitable for the already checked
strong-induction schema. The only distinguished free induction term is the
payload; the original packed input is NOT held fixed during induction. -/
def atPayload {α : Type} (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload : OrdinaryArithmetic.Term α) : Formula α :=
  InternalClosedPrograms.allBlock (payloadMatrix old representative member payload)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariant
