module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapConsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions

public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (allOne existsOne)
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)

def originRow {α : Type} (code key row : OTerm α) : Formula α :=
  memberGraph code row ⊓ (unary (guardAt 4) (suc z) row ⊓ unary (field 0) key row)

def originBody {α : Type} (code key : OTerm α) : Formula (α ⊕ Fin 1) :=
  originRow (code.relabel Sum.inl) (key.relabel Sum.inl) (.var (.inr 0))

def origin {α : Type} (code key : OTerm α) : Formula α := existsOne (originBody code key)

def atOutput {α : Type} (code key out : OTerm α) : Formula α :=
  (unary scratchTargets (suc out) code ⊓ memberGraph out key).imp (origin code key)

def allOutputsBody {α : Type} (code key : OTerm α) : Formula (α ⊕ Fin 1) :=
  atOutput (code.relabel Sum.inl) (key.relabel Sum.inl) (.var (.inr 0))

def allOutputs {α : Type} (code key : OTerm α) : Formula α := allOne (allOutputsBody code key)

def motive {α : Type} (key : OTerm α) : Formula (α ⊕ Fin 1) :=
  allOutputs (.var (.inr 0)) (key.relabel Sum.inl)

/-- Every real member of the actual successful map output comes from a
genuine original input member with the actual tag-4 and field-zero reports.
Object existential, pointwise (not occurrence indices or counts). -/
def ExactOpenProjectedTargetOrigin : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (input output key : OTerm α),
    Nonempty (Derivation B Γ (atOutput input key output))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapOriginTargets
