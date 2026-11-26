module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.RelationFold
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership

def fields {k : Nat} (base : Program k) (step : Program (k+2)) (transform : Program (k+2))
    {alpha : Type} (raw needle image out : OTerm alpha) (params : Fin k → OTerm alpha) : Formula alpha :=
  programGraph (InternalRawListRecursion.listRec base step) out (Fin.cons raw params) ⊓
    (programGraph transform (SourceComputabilityFormulaSupportProof.numeral 1) (Fin.cons image (Fin.cons needle params)) ⊓ graph2 contains (numeral 1) raw needle)
def result {alpha : Type} (out image : OTerm alpha) : Formula alpha := graph2 contains (numeral 1) out image

def matrix {k : Nat} (base : Program k) (step : Program (k+2)) (transform : Program (k+2))
    {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin (k+3)) :=
  (fields base step transform (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (fun i => .var (.inr i.succ.succ.succ))).imp (result (.var (.inr 2)) (.var (.inr 1)))
def AtRaw {k : Nat} (base : Program k) (step : Program (k+2)) (transform : Program (k+2))
    {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix base step transform raw)
def rawPredicate {k : Nat} (base : Program k) (step : Program (k+2)) (transform : Program (k+2))
    {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw base step transform (.var (.inr 0))
def BelowRaw {k : Nat} (base : Program k) (step : Program (k+2)) (transform : Program (k+2))
    {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate base step transform) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.RelationFold
