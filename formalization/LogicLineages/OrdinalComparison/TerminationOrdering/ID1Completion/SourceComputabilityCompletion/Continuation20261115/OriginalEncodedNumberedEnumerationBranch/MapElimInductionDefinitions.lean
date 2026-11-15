module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapImageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable (F : Program 1)
open InternalTagArithmeticSyntaxProof (z eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Actual output membership has an internal preimage, not a supplied native image.
Three unused slots retain the checked five-variable binding scaffold. -/
def fields {alpha : Type} (raw param out node sourceChild targetChild : OTerm alpha) : Formula alpha :=
  graph1 (InternalListMap.map F) out raw ⊓ graph2 contains (numeral 1) out node
def result {alpha : Type} (raw param out node sourceChild targetChild : OTerm alpha) : Formula alpha :=
  MapImageProof.image F raw node
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (fields F (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))).imp
  (result F (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix F raw)
def rawPredicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw F (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate F) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.MapElimInductionDefinitions
