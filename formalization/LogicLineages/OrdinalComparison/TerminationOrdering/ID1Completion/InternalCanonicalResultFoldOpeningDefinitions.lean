module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpening
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All selectors read the WHOLE original input, before any normalization.
The codomain is its actual raw LEFT field, not a reconstructed child tag. -/
def rootDomain : Program 1 := InternalApplicationStepPeel.appDomain (.projection 0)
def rootCodomain : Program 1 := leftOf (.projection 0)
def functionChild : Program 1 :=
  pairOf (consOf rootDomain rootCodomain)
    (InternalApplicationStepPeel.functionPayload (.projection 0))
def argumentChild : Program 1 :=
  pairOf rootDomain (InternalApplicationStepPeel.argumentPayload (.projection 0))

/-- Exactly V(root), V(original function child), V(original argument child),
and member(original codomain), in that order. Every conjunction accepts only
the value ONE. ResultStack.openGuard supplies the separate constructor-tag-2
test; G alone is not claimed to equal V on non-application inputs. -/
def rootGuard (valid member : Program 1) : Program 1 :=
  InternalAcceptance.conjunction valid
    (InternalAcceptance.conjunction
      (.composition valid (fun _ : Fin 1 => functionChild))
      (InternalAcceptance.conjunction
        (.composition valid (fun _ : Fin 1 => argumentChild))
        (.composition member (fun _ : Fin 1 => rootCodomain))))

/-- D is the checked bounded-descent selection with the ORIGINAL R fallback. -/
def leaf (representative valid : Program 1) : Program 1 :=
  InternalCanonicalDescentSelection.fallbackRepresentative representative valid

/-- Inputs remain [domain,codomain,functionOutput,argumentOutput]. Apply D
to the ORIGINAL raw application of the two whole child outputs. In particular
this is not the older codomain-repacking combine, and it does not normalize
the original children before rootGuard inspects them. -/
def combine (representative valid : Program 1) : Program 4 :=
  .composition (leaf representative valid) (fun _ : Fin 1 => application)

/-- Concrete aliases only. No fold invariant, calibration, or successful-run
law is asserted by this opening prerequisite. Fuel stays 2*input-payload+1. -/
def foldN (representative valid member : Program 1) : Program 1 :=
  InternalApplicationResultStack.fold (rootGuard valid member)
    (leaf representative valid) (combine representative valid)

def goodRunH (representative valid member : Program 1) : Program 1 :=
  InternalApplicationCertifiedResultFoldClosure.goodRun (rootGuard valid member)
    (leaf representative valid) (combine representative valid)

/-- Actual full opening acceptance, including the unchanged tag-2 wrapper. -/
def openingAccepted {α : Type} (valid member : Program 1)
    (parent : OrdinaryArithmetic.Term α) : Formula α :=
  graph1 (InternalApplicationResultStack.openGuard (rootGuard valid member))
    InternalOriginalStepGuard.one parent

/-- Four actual exact-one graphs. All are conclusions of opening acceptance,
including the original root and BOTH original children. -/
def validityFactors {α : Type} (valid member : Program 1)
    (parent fn arg e : OrdinaryArithmetic.Term α) : Formula α :=
  graph1 valid InternalOriginalStepGuard.one parent ⊓
    (graph1 valid InternalOriginalStepGuard.one fn ⊓
      (graph1 valid InternalOriginalStepGuard.one arg ⊓
        graph1 member InternalOriginalStepGuard.one e))

/-- Explicit original selectors for the parent and reconstructed children.
These expose the payloads needed by a later strong-payload induction, rather
than imposing a false size bound on packed child codes or normalized outputs. -/
def originalFields {α : Type}
    (parent payload arrow d e fp ap fn arg : OrdinaryArithmetic.Term α) : Formula α :=
  graph1 InternalUnpair.left e parent ⊓
    (graph1 InternalUnpair.right payload parent ⊓
      (graph1 InternalUnpair.left arrow fn ⊓
        (graph1 InternalUnpair.right fp fn ⊓
          (graph1 InternalUnpair.left d arg ⊓
            graph1 InternalUnpair.right ap arg))))

/-- A shared original opening, with NO semantic decode, calibration, source
inversion, successful child run, normalized output, or induction hypothesis.
The original arrow/application constructors and both strict payload bounds
must all be produced internally from the accepted opening. -/
def openingWitnesses {α : Type} (valid member : Program 1)
    (parent payload middle children arrow d e fp ap fn arg : OrdinaryArithmetic.Term α) :
    Formula α :=
  InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
    (validityFactors valid member parent fn arg e ⊓
      (originalFields parent payload arrow d e fp ap fn arg ⊓
        (InternalPairingSumBounds.applicationPayloadWitnesses payload middle children d fp ap ⊓
          (InternalLessThan.strictLess fp payload ⊓ InternalLessThan.strictLess ap payload))))

/-- Bound witness order: payload, middle, children, arrow, domain, codomain,
function payload, argument payload, function code, argument code. The sole
free input is the original parent, retained by the existing relabel operation. -/
def openingMatrix {α : Type} (valid member : Program 1)
    (parent : OrdinaryArithmetic.Term α) : Formula (α ⊕ Fin 10) :=
  let w : Fin 10 → OrdinaryArithmetic.Term (α ⊕ Fin 10) := fun i => .var (.inr i)
  openingWitnesses valid member (parent.relabel Sum.inl)
    (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9)

/-- The existing object-language existential block, not metatheoretic choice
of semantic natural numbers or an added inversion/success premise. -/
def opened {α : Type} (valid member : Program 1)
    (parent : OrdinaryArithmetic.Term α) : Formula α :=
  InternalFiniteBlocks.block (openingMatrix valid member parent)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpening
