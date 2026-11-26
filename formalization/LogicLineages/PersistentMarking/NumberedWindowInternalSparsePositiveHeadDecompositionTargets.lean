module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveDeadCurrentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalFiniteBlocks (block)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldInductionTargets (consGraph)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparsePositiveFold (finish positive)
open NumberedWindowInternalSparsePositiveOutputTargets (args4 args5 equivalent)

def positiveAt {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source certificate target : OTerm α) : Formula α :=
  programGraph (positive raw least) (suc z) (args5 ctx ty source certificate target)

def finishAt {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source certificate target : OTerm α) : Formula α :=
  programGraph (finish raw least) (suc target) (args4 ctx ty (suc source) certificate)

def finishedNonempty {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source certificate target : OTerm α) : Formula α :=
  (equal certificate z).not ⊓ finishAt raw least ctx ty source certificate target

/-- Exactly the first raw cell, a genuine successful encoded result of
its actual advance, and the actual chosen-fuel tail success at that
class. Tail zero is allowed; no tail-positive formula is used. -/
def headData {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source certificate target head tail nextClass : OTerm α) : Formula α :=
  consGraph certificate head tail ⊓
    (selectedGraph raw least (suc nextClass) ctx ty (suc source) head ⊓
      finishAt raw least ctx ty nextClass tail target)

def headRow {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source certificate target : OTerm α) : Formula (α ⊕ Fin 3) :=
  let j : α → α ⊕ Fin 3 := Sum.inl
  headData raw least (ctx.relabel j) (ty.relabel j) (source.relabel j)
    (certificate.relabel j) (target.relabel j) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))

/-- Genuine object existential block, in order [raw head,raw tail,next
class]. Neither successful data nor preexisting validity is a premise. -/
def hasAcceptedHead {α : Type} (raw : Program 5) (least : Program 3)
    (ctx ty source certificate target : OTerm α) : Formula α :=
  block (headRow raw least ctx ty source certificate target)

def OpenPositiveFinish : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (ctx ty source certificate target : OTerm α),
    Nonempty (Derivation body [] (equivalent
      (positiveAt raw least ctx ty source certificate target)
      (finishedNonempty raw least ctx ty source certificate target)))

def OpenPositiveHeadDecomposition : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (ctx ty source certificate target : OTerm α),
    Nonempty (Derivation body [] (equivalent
      (positiveAt raw least ctx ty source certificate target)
      (hasAcceptedHead raw least ctx ty source certificate target)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionTargets
