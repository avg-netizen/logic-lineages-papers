module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalTagArithmeticSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalOriginalOrderSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalContextInsertionBelowSyntaxProof OriginalContextInsertionBelowInductionProof
open OriginalVariableDecoderGraphSupportProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

 theorem belowWitnesses (out typ index d cutoff gamma extended front suffix inserted : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma
      (witnesses d cutoff gamma extended front suffix inserted)))
    (hb : Nonempty (Derivation body Gamma (Below index cutoff))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ index gamma).iff
        (OriginalVariableDecoder.graph out typ index extended))) :=
  samePrefixBelow front out typ cutoff suffix gamma inserted extended index
    (andLeft hw) (andLeft (andRight hw)) (andRight (andRight (andRight hw))) hb

 theorem variableBelow (out typ index d cutoff gamma extended : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma (Insert d cutoff gamma extended)))
    (hb : Nonempty (Derivation body Gamma (Below index cutoff))) :
    Nonempty (Derivation body Gamma
      ((OriginalVariableDecoder.graph out typ index gamma).iff
        (OriginalVariableDecoder.graph out typ index extended))) := by
  apply insertCases d cutoff gamma extended _ hi
  intro beta j Delta front suffix inserted hj hw
  rw [iffRename,graphRename,graphRename]
  have hb' := renameInto hb j Delta hj
  change Nonempty (Derivation body Delta ((ltF index cutoff).relabel j)) at hb'
  rw [orderRename] at hb'
  exact belowWitnesses _ _ _ _ _ _ _ front suffix inserted hw hb'

 theorem actualOriginalContextInsertionVariableBelow :
    OriginalContextInsertionTargets.ActualOriginalContextInsertionVariableBelow := by
  intro body alpha out typ index d cutoff gamma extended
  let A := Insert d cutoff gamma extended ⊓ Below index cutoff
  have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := variableBelow out typ index d cutoff gamma extended (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowProof
