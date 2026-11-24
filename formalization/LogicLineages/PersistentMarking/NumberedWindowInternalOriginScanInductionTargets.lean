module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginFilterConsCasesTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedHeadTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalClosedPrograms
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalOriginFilterConsCasesTargets (filterGraph)
open NumberedWindowInternalOpenOriginScanIntroTargets (D)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalDirectTypedUnionScratchTargets (observer)
open NumberedWindowInternalLiteralCount (permutation)

def goalAt {α : Type} (r : Program 3) (rawL rawR outL outR : OTerm α) : Formula α :=
  loopAccept r outL rawL ⊓ loopAccept r outR rawR

def suppliedAt {α : Type} (r : Program 3)
    (rows removed rawL rawR scratchL outL outR : OTerm α) : Formula α :=
  (loopAccept r rows removed ⊓
    (filterGraph true outL rows scratchL ⊓ filterGraph false outR rows scratchL)).imp
      (goalAt r rawL rawR outL outR)

def matrix {α : Type} (r : Program 3) (rows removed rawL rawR scratchL : OTerm α) :
    Formula (α ⊕ Fin 2) :=
  suppliedAt r (rows.relabel Sum.inl) (removed.relabel Sum.inl)
    (rawL.relabel Sum.inl) (rawR.relabel Sum.inl) (scratchL.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1))

def atRows {α : Type} (r : Program 3) (rows removed rawL rawR scratchL : OTerm α) : Formula α :=
  allBlock (matrix r rows removed rawL rawR scratchL)

abbrev motive {α : Type} (r : Program 3) (removed rawL rawR scratchL : OTerm α) :
    Formula (α ⊕ Fin 1) :=
  atRows r (.var (.inr 0)) (removed.relabel Sum.inl)
    (rawL.relabel Sum.inl) (rawR.relabel Sum.inl) (scratchL.relabel Sum.inl)

structure Pools (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (removed decoded rawL rawR scratchL scratchR joined : OTerm α) : Prop where
  oldParsed : D B Γ (unary parser (suc decoded) removed)
  leftParsed : D B Γ (unary parser (suc scratchL) rawL)
  rightParsed : D B Γ (unary parser (suc scratchR) rawR)
  count : D B Γ (observer permutation decoded joined)
  appended : D B Γ (appendGraph joined scratchL scratchR)

def ExactOpenOriginScanAtRows : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (rows removed decoded rawL rawR scratchL scratchR joined outL outR : OTerm α),
    Pools B Γ removed decoded rawL rawR scratchL scratchR joined →
    D B Γ (loopAccept r rows removed) →
    D B Γ (filterGraph true outL rows scratchL) →
    D B Γ (filterGraph false outR rows scratchL) →
    D B Γ (goalAt r rawL rawR outL outR)

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionTargets
