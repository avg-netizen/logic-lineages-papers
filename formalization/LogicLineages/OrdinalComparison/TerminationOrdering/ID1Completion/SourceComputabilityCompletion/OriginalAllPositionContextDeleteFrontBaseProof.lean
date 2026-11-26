module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontBaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof
open InternalListCodecSupportProof InternalRecursionClosureLogicProof
open OriginalClassContextAllPositionObserver OriginalAllPositionContextDeleteFrontSyntaxProof
open OriginalAllPositionContextDeleteBaseProof OriginalAllPositionContextDeleteFrontStepProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (gamma head tail previous out : InternalGraphComposition.OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hp : Nonempty (Derivation body Delta (graph2 front previous z tail)))
    (ho : Nonempty (Derivation body Delta (consGraph out head previous))) :
    Nonempty (Derivation body Delta (graph2 front out (suc z) gamma)) := by
  have he := valueUnique front previous z (Fin.cons z (Fin.cons tail Fin.elim0)) hp (frontZero tail)
  have hsingle := OriginalContextInsertionSupportProof.binaryInputs InternalListCodec.consCode out head previous head z ⟨refl _⟩ he ho
  exact frontNext z z gamma head out out (frontZero gamma) (lookupZero gamma head tail hc)
    hsingle (InternalApplicationValidityStackAppendListProof.appendZeroValue out)

theorem zeroRow : Nonempty (Derivation body Delta (row (z : InternalGraphComposition.OTerm alpha))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 5 Delta
  let gamma : InternalGraphComposition.OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let head : InternalGraphComposition.OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let tail : InternalGraphComposition.OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let previous : InternalGraphComposition.OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let out : InternalGraphComposition.OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let A := consGraph gamma head tail ⊓ (graph2 front previous z tail ⊓ consGraph out head previous)
  have h : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := zeroCore gamma head tail previous out
    (InternalApplicationStepPeelSupportProof.andLeft h)
    (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight h))
    (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight h))
  simpa only [rowBody,zRelabel] using Nonempty.intro (Derivation.implicationIntroduction hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontBaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontBaseProof
