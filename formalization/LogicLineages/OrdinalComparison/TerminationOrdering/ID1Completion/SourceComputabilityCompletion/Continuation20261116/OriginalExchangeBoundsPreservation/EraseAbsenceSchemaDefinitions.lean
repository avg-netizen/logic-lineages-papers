module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceSchema
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def fields (S : Program 2) {alpha : Type} (raw needle acc bit rest : OTerm alpha) : Formula alpha :=
  graph2 S acc raw needle ⊓ graph2 InternalPairing.pairing acc bit rest
def result (C : Program 2) {alpha : Type} (raw needle bit : OTerm alpha) : Formula alpha :=
  (eqn bit z).imp (graph2 C z raw needle)
def matrix (C S : Program 2) {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  let x : Fin 4 → OTerm (alpha ⊕ Fin 4) := fun i => .var (.inr i)
  (fields S (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3)).imp
    (result C (raw.relabel Sum.inl) (x 0) (x 2))
def AtRaw (C S : Program 2) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix C S raw)
def predicate (C S : Program 2) {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw C S (.var (.inr 0))
def BelowRaw (C S : Program 2) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (predicate C S) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceSchema
