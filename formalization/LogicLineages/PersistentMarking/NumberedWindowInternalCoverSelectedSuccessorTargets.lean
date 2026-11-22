module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalPairing (pairing)
open ID1Completion.InternalUnpair (left right)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCoverAlgorithm (leaves lambdas ordinary numbered applications cells)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverAuxApplicationsTargets (auxApplications binary reorder)
open NumberedWindowInternalCoverNamedLeavesTargets (namedFromIds)
open NumberedWindowInternalCoverOrdinaryLayerTargets (ordinaryLayer)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedLayer)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeaves)
open NumberedWindowInternalCoverArgumentCellsTargets (cellsAt axisInclusion)

/-- Tape is always the genuine ordered [H,K,IDs,old terms,old args].
Its IDs are already an actual list; there is no hidden range call. -/
def freePart : Program 5 := reorder (namedFromIds 0) ![1,2]
def boundPart : Program 5 := reorder (namedFromIds 1) ![1,2]
def typePart : Program 5 := reorder typeLeaves ![1]
def lambdaPart : Program 5 := reorder (namedFromIds 2) ![1,3]
def ordinaryPart : Program 5 := reorder ordinaryLayer ![0,4]
def numberedPart : Program 5 := reorder numberedLayer ![0,1,2,4]
def auxiliaryPart : Program 5 := reorder auxApplications ![1,3]

def join (P Q : Program 5) : Program 5 := binary append P Q

def namedPart : Program 5 := join freePart boundPart
def leavesPart : Program 5 := join namedPart typePart
def throughLambda : Program 5 := join leavesPart lambdaPart
def throughOrdinary : Program 5 := join throughLambda ordinaryPart
def nonAuxPart : Program 5 := join throughOrdinary numberedPart

def termsPart : Program 5 := join nonAuxPart auxiliaryPart
def argsPart : Program 5 := reorder cellsAt ![3,4]

/-- The actual original next-term and next-argument scratch codes are
retained in an unshifted standard pairing, not a sparse argument cell. -/
def selectedStep : Program 5 := binary pairing termsPart argsPart

def termsValue (H K ids ts args : List Nat) : List Nat :=
  leaves K ids ++ lambdas K ts ++ ordinary H args ++ numbered H K ids args ++ applications K ts

abbrev stepTape {α : Type} (H K ids ts args : OTerm α) : Fin 5 → OTerm α := ![H,K,ids,ts,args]

abbrev stepReport {α : Type} (P : Program 5) (out H K ids ts args : OTerm α) : Formula α :=
  programGraph P out (stepTape H K ids ts args)

abbrev termProjection {α : Type} (out state : OTerm α) : Formula α := unary left out state
abbrev argsProjection {α : Type} (out state : OTerm α) : Formula α := unary right out state

def ExactSelectedCoverNonAuxValue : Prop :=
  ∀ H K ids ts args : List Nat,
    evaluate nonAuxPart (numbersNumber H ::ᵥ numbersNumber K ::ᵥ numbersNumber ids ::ᵥ
      numbersNumber ts ::ᵥ numbersNumber args ::ᵥ nil) =
    numbersNumber (leaves K ids ++ lambdas K ts ++ ordinary H args ++ numbered H K ids args)

def ExactSelectedCoverSuccessorValue : Prop :=
  ∀ H K ids ts args : List Nat,
    evaluate selectedStep (numbersNumber H ::ᵥ numbersNumber K ::ᵥ numbersNumber ids ::ᵥ
      numbersNumber ts ::ᵥ numbersNumber args ::ᵥ nil) =
    Nat.pair (numbersNumber (termsValue H K ids ts args)) (numbersNumber (cells ts args))

/-- Keep H and K literally shared. The other three components each
have only an actual object membership-inclusion hypothesis. -/
def OpenPartInclusion (P : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (old next H K ids ids' ts ts' args args' : OTerm α),
  Nonempty (Derivation body Γ (stepReport P old H K ids ts args)) →
  Nonempty (Derivation body Γ (stepReport P next H K ids' ts' args')) →
  Nonempty (Derivation body Γ (axisInclusion ids ids')) →
  Nonempty (Derivation body Γ (axisInclusion ts ts')) →
  Nonempty (Derivation body Γ (axisInclusion args args')) →
  Nonempty (Derivation body Γ (axisInclusion old next))

/-- Resolve both actual observed output codes from the one selected
pair report and its actual ordinary unpair calls. -/
def ExactOpenSelectedCoverSuccessorSplit : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (state outTerms outArgs H K ids ts args : OTerm α),
  Nonempty (Derivation body Γ (stepReport selectedStep state H K ids ts args)) →
  Nonempty (Derivation body Γ (termProjection outTerms state)) →
  Nonempty (Derivation body Γ (argsProjection outArgs state)) →
  Nonempty (Derivation body Γ
    (stepReport termsPart outTerms H K ids ts args ⊓ stepReport argsPart outArgs H K ids ts args))

/-- Exactly one actual selected successor on each tape; no earlier or
recursive grammar-report transport is assumed or asserted. -/
def ExactOpenSelectedCoverSuccessorInclusion : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (old next oldTerms nextTerms oldArgs nextArgs H K ids ids' ts ts' args args' : OTerm α),
  Nonempty (Derivation body Γ (stepReport selectedStep old H K ids ts args)) →
  Nonempty (Derivation body Γ (stepReport selectedStep next H K ids' ts' args')) →
  Nonempty (Derivation body Γ (termProjection oldTerms old)) →
  Nonempty (Derivation body Γ (termProjection nextTerms next)) →
  Nonempty (Derivation body Γ (argsProjection oldArgs old)) →
  Nonempty (Derivation body Γ (argsProjection nextArgs next)) →
  Nonempty (Derivation body Γ (axisInclusion ids ids')) →
  Nonempty (Derivation body Γ (axisInclusion ts ts')) →
  Nonempty (Derivation body Γ (axisInclusion args args')) →
  Nonempty (Derivation body Γ (axisInclusion oldTerms nextTerms ⊓ axisInclusion oldArgs nextArgs))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorTargets
