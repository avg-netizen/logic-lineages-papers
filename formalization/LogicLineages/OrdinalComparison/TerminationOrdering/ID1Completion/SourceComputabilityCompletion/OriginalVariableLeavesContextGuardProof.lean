module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientDecoderProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesContextGuardProof
open OriginalVariableLeaves
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

/-- The guard compiles the actual original finite-table Context decoder. -/
theorem contextGuardPrimitive (n : Nat) :
    Primrec (fun v : List.Vector Nat 1 =>
      (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (v.get 0)).isSome.toNat) := by
  exact (Primrec.dom_bool Bool.toNat).comp
    (Primrec.option_isSome.comp
      ((OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp
        (Primrec.vector_get.comp Primrec.id (Primrec.const 0))))

theorem actualOriginalVariableContextGuardSelection :
    OriginalVariableLeavesTargets.ActualOriginalVariableContextGuardSelection := by
  intro n
  exact Proof.allPrimitiveFunctions 1 _ (contextGuardPrimitive n)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesContextGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesContextGuardProof
