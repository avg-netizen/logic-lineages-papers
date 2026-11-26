module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyActiveProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSyntaxProof (z)
open UniformCertificateCompletion OriginalStructuralClassKeyDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem keyToCore (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (value out parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (Active p H G W value parameter)))
    (hk : Nonempty (Derivation body Delta (graph2 (key p H G W) out value parameter))) :
    Nonempty (Derivation body Delta (graph2 (core p H G W) out value parameter)) :=
  InternalAcceptanceBranchProof.successorBranchElim (active p H G W)
    (prior p H G W).base.oldRepresentative (core p H G W) out z
    (Fin.cons value (Fin.cons parameter Fin.elim0)) ha hk

theorem coreToKey (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (value out parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (Active p H G W value parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (core p H G W) out value parameter))) :
    Nonempty (Derivation body Delta (graph2 (key p H G W) out value parameter)) :=
  InternalAcceptanceBranchProof.successorBranchIntro (active p H G W)
    (prior p H G W).base.oldRepresentative (core p H G W) out z
    (Fin.cons value (Fin.cons parameter Fin.elim0)) ha hc

theorem actualOriginalStructuralClassKeyActiveCore :
    OriginalStructuralClassKeyTargets.ActualOriginalStructuralClassKeyActiveCore := by
  intro p H G W body alpha Delta value out parameter
  let A := Active p H G W value parameter
  let K := graph2 (key p H G W) out value parameter
  let C := graph2 (core p H G W) out value parameter
  have haK : Nonempty (Derivation body (K :: A :: Delta) A) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have haC : Nonempty (Derivation body (C :: A :: Delta) A) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := keyToCore p H G W value out parameter haK
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := coreToKey p H G W value out parameter haC
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyActiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralClassKeyActiveProof
