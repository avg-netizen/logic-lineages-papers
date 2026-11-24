module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedTargetsMapTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapIntroTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedTargetsMapTargets (targetStep scratchTargets insertedTargets)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseFieldParser (parser)

abbrev D {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

def ExactOpenTargetProjectionNil : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)),
    D B Γ (unary scratchTargets (suc z) z)

def ExactOpenTargetProjectionStepIntro : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (row target prior out : OTerm α),
    D B Γ (unary (guardAt 4) (suc z) row) →
    D B Γ (unary (field 0) target row) →
    D B Γ (consGraph out target prior) →
    D B Γ (programGraph targetStep (suc out) ![row,suc prior])

def ExactOpenRawTargetProjectionIntro : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (raw scratch projected : OTerm α),
    D B Γ (unary parser (suc scratch) raw) →
    D B Γ (unary scratchTargets (suc projected) scratch) →
    D B Γ (unary insertedTargets (suc projected) raw)

abbrev projectedBody {α : Type} (rows : OTerm α) : Formula (α ⊕ Fin 1) :=
  unary scratchTargets (suc (.var (.inr 0))) (rows.relabel Sum.inl)

abbrev hasProjection {α : Type} (rows : OTerm α) : Formula α :=
  existsOne (projectedBody rows)

abbrev atRows {α : Type} (r : Program 3) (rows removed : OTerm α) : Formula α :=
  (loopAccept r rows removed).imp (hasProjection rows)

abbrev motive {α : Type} (r : Program 3) (removed : OTerm α) : Formula (α ⊕ Fin 1) :=
  atRows r (.var (.inr 0)) (removed.relabel Sum.inl)

def ExactOpenAcceptedScanHasProjection : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (rows removed : OTerm α), D B Γ (atRows r rows removed)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapIntroTargets
