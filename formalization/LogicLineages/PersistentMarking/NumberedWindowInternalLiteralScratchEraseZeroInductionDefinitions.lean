module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseZeroInductionDefinitions
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralScratchErase (state)
open InternalTagArithmeticSyntaxProof (eqn z)

def fields {alpha : Type} (raw needle acc bit rest : OTerm alpha) : Formula alpha :=
  graph2 state acc raw needle ⊓ graph2 InternalPairing.pairing acc bit rest
def zeroIdentity {alpha : Type} (raw bit rest : OTerm alpha) : Formula alpha :=
  (eqn bit z).imp (eqn rest raw)
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  let x : Fin 4 → OTerm (alpha ⊕ Fin 4) := fun i => .var (.inr i)
  (fields (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3)).imp
    (zeroIdentity (raw.relabel Sum.inl) (x 2) (x 3))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix raw)
def predicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below predicate raw
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseZeroInductionDefinitions
