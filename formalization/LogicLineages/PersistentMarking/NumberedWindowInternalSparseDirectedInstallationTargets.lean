module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseInstalledOccurrenceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgeTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedInstallationTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenA)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseTypedRawTargets (ActualRawSyntax ActualPackedWindow)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)

open ID1Completion.InternalControlGraph (programGraph)
open ID1Completion.InternalLessThan (strictLess)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFuelBudgetTargets (runsAt)
open NumberedWindowInternalSparseDirectedRounds (poolLength members membersTape)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparseInstalledOccurrenceTargets (OpenCoverAt)

def ExactLengthCutoff : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed size before after : OTerm α),
    Nonempty (Derivation body Γ ((unary poolLength size vertices ⊓
      runsAt E size vertices ctx ty seed before after).imp (PrimaryMonotonicity.included after before)))

/-- The actual members output is closed under every accepted directed edge
from a contained source to a destination among the same original vertices. -/
def ExactDirectedMembersClosure : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (vertices ctx ty seed pool source target : OTerm α),
    let run := programGraph (members E) pool (membersTape vertices ctx ty seed)
    let edge := (memberGraph pool source ⊓ acceptEdge E ctx ty source target) ⊓ memberGraph vertices target
    Nonempty (Derivation body Γ ((run ⊓ edge).imp (memberGraph pool target)))


def MinimumEdgeAt (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed minimum target : OTerm α),
    Nonempty (Derivation body Γ ((leastGraph C X W s ctx ty seed minimum ⊓
      (acceptEdge (edge4 X W) ctx ty minimum target ⊓ occursInCover C s seed target)).imp
      (strictLess target minimum).not))

def PositiveEndpointsAt (raw : Program 5) (least W : Program 3) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty source cert target : OTerm α),
    Nonempty (Derivation body Γ ((positiveAt raw least ctx ty source cert target).imp
      (windowAt W ctx ty source ⊓ windowAt W ctx ty target)))

/-- The same chosen exchange and window programs are used at all open inputs,
including by the least program installed in the final application tuple. -/
def ExactDirectedInstallation : Prop :=
  ∃ C : Program 3, ActualSelectedCoverOutput C ∧
    ∀ (entries : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
      ∃ (i j cv tv syntaxProg : Program 1) (X : Program 2)
        (d oldCore oldLeast root other windowProg : Program 3) (v : Inputs),
        ActualRoot (NumberedWindowConcreteCheckers.root entries s) root ∧
        ActualFallback other ∧ ActualRawSyntax syntaxProg ∧ ActualPackedWindow s windowProg ∧
        ActualTermExchange s X ∧
        let raw := typedRaw5 root other windowProg syntaxProg
        let least := packedLeastProgram C X windowProg s
        let updated := frontendInputs i least v
        ActualLeastCalibration s least ∧
        InstalledTupleAt entries s W i j cv tv d oldCore raw oldLeast v ∧
        InstalledTupleAt entries s W i j cv tv d oldCore raw least v ∧
        chosenA updated = chosenA v ∧
        InstalledTupleAt entries s W i j cv tv d (applicationCore least) raw least updated ∧
        OpenCoverAt C X windowProg s ∧ MinimumEdgeAt C X windowProg s ∧
        PositiveEndpointsAt raw least windowProg

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedInstallationTargets
