module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldLeafClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldLeafClosureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertifiedResultFoldClosure InternalApplicationCertifiedResultFoldLeafClosure
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Genuine INTERNAL leaf closure for arbitrary Programs, positive bodies,
contexts and symbolic terms. The two actual leaf-branch graphs imply BOTH
actual goodRun acceptance and the actual unchanged fold output. The run keeps
its original succ(payload+payload) fuel. Payload, singleton work/results and
state witnesses must be introduced internally, not supplied as premises.
Zero is an allowed output. No semantic calibration or reflection is assumed. -/
def ActualOriginalCertifiedResultFoldLeafClosure : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 1) (combine : Program 4)
    (α : Type) (Gamma : List (Formula α)) (value out : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((leafGraphs guard leaf out value).imp (certifiedFold guard leaf combine out value)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldLeafClosureTargets
