module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.LayerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (sucNeZeroApply)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 ExchangeLayer ExchangeLayer.InternalSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem tagReject (k : Nat) (xs : Fin 19 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (eqn (xs 0) (numeral k)).not)) :
    Nonempty (Derivation body Delta (programGraph (tagIs k) z xs)) := by
  have hz := OriginalRawSyntaxTransportInternalConstructorSupportProof.sameReject
    (.projection 0) (OriginalRawSyntaxTransport.constant 19 k) (xs 0) (numeral k) xs
    (projectionValue 0 xs) (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue k xs)
    (by simpa only [InternalControlGraphSupportProof.equalEqn] using h)
  simpa only [tagIs,constantEq,OriginalRawSyntaxTransport.sameOf] using hz

theorem equalTags (xs : Fin 19 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (programGraph layer (numeral 1) xs))) :
    Nonempty (Derivation body Delta (eqn (xs 0) (xs 7))) := by
  let A := eqn (xs 0) (xs 7)
  apply formulaCases A A
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have hn : Nonempty (Derivation body (A.not :: Delta) A.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hn⟩ := ExchangeLayer.LambdaProof.internalTagMismatch body alpha (A.not :: Delta) xs hn
    obtain ⟨hh⟩ := withHyp h A.not
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn hh)⟩

theorem at7 (xs : Fin 19 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (programGraph (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19)) (numeral 1) xs))) :
    Nonempty (Derivation body Delta (eqn (xs 0) (numeral 7))) := by
  let A := eqn (xs 0) (numeral 7)
  apply formulaCases A (eqn (xs 0) (numeral 7))
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have hn : Nonempty (Derivation body (A.not :: Delta) A.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := tagReject 7 xs hn
    have ht := zeroBranchElim (tagIs 7) (InternalAcceptance.constantZero 19) applicationCase (numeral 1) xs hz (withHyp h A.not)
    obtain ⟨he⟩ := valueUnique (InternalAcceptance.constantZero 19) (numeral 1) z xs ht
      (InternalAcceptanceConjunctionProof.constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩

theorem at5 (xs : Fin 19 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (programGraph (choose (tagIs 5) numberedCase (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19))) (numeral 1) xs))) :
    Nonempty (Derivation body Delta ((eqn (xs 0) (numeral 5) ⊔ eqn (xs 0) (numeral 7)))) := by
  let A := eqn (xs 0) (numeral 5)
  apply formulaCases A ((eqn (xs 0) (numeral 5) ⊔ eqn (xs 0) (numeral 7)))
  · exact ⟨InternalQuotientComparisonProof.orLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · have hn : Nonempty (Derivation body (A.not :: Delta) A.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := tagReject 5 xs hn
    have ht := zeroBranchElim (tagIs 5) (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19)) numberedCase (numeral 1) xs hz (withHyp h A.not)
    obtain ⟨hout⟩ := at7 xs ht
    exact ⟨InternalQuotientComparisonProof.orRight hout⟩

theorem at4 (xs : Fin 19 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (programGraph (choose (tagIs 4) ordinaryCase (choose (tagIs 5) numberedCase (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19)))) (numeral 1) xs))) :
    Nonempty (Derivation body Delta ((eqn (xs 0) (numeral 4) ⊔ (eqn (xs 0) (numeral 5) ⊔ eqn (xs 0) (numeral 7))))) := by
  let A := eqn (xs 0) (numeral 4)
  apply formulaCases A ((eqn (xs 0) (numeral 4) ⊔ (eqn (xs 0) (numeral 5) ⊔ eqn (xs 0) (numeral 7))))
  · exact ⟨InternalQuotientComparisonProof.orLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · have hn : Nonempty (Derivation body (A.not :: Delta) A.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := tagReject 4 xs hn
    have ht := zeroBranchElim (tagIs 4) (choose (tagIs 5) numberedCase (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19))) ordinaryCase (numeral 1) xs hz (withHyp h A.not)
    obtain ⟨hout⟩ := at5 xs ht
    exact ⟨InternalQuotientComparisonProof.orRight hout⟩

theorem at2 (xs : Fin 19 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (programGraph (choose (tagIs 2) applicationCase (choose (tagIs 4) ordinaryCase (choose (tagIs 5) numberedCase (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19))))) (numeral 1) xs))) :
    Nonempty (Derivation body Delta ((eqn (xs 0) (numeral 2) ⊔ (eqn (xs 0) (numeral 4) ⊔ (eqn (xs 0) (numeral 5) ⊔ eqn (xs 0) (numeral 7)))))) := by
  let A := eqn (xs 0) (numeral 2)
  apply formulaCases A ((eqn (xs 0) (numeral 2) ⊔ (eqn (xs 0) (numeral 4) ⊔ (eqn (xs 0) (numeral 5) ⊔ eqn (xs 0) (numeral 7)))))
  · exact ⟨InternalQuotientComparisonProof.orLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · have hn : Nonempty (Derivation body (A.not :: Delta) A.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := tagReject 2 xs hn
    have ht := zeroBranchElim (tagIs 2) (choose (tagIs 4) ordinaryCase (choose (tagIs 5) numberedCase (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19)))) applicationCase (numeral 1) xs hz (withHyp h A.not)
    obtain ⟨hout⟩ := at4 xs ht
    exact ⟨InternalQuotientComparisonProof.orRight hout⟩

theorem at1 (xs : Fin 19 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (programGraph (choose (tagIs 1) lambdaCase (choose (tagIs 2) applicationCase (choose (tagIs 4) ordinaryCase (choose (tagIs 5) numberedCase (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19)))))) (numeral 1) xs))) :
    Nonempty (Derivation body Delta ((eqn (xs 0) (numeral 1) ⊔ (eqn (xs 0) (numeral 2) ⊔ (eqn (xs 0) (numeral 4) ⊔ (eqn (xs 0) (numeral 5) ⊔ eqn (xs 0) (numeral 7))))))) := by
  let A := eqn (xs 0) (numeral 1)
  apply formulaCases A ((eqn (xs 0) (numeral 1) ⊔ (eqn (xs 0) (numeral 2) ⊔ (eqn (xs 0) (numeral 4) ⊔ (eqn (xs 0) (numeral 5) ⊔ eqn (xs 0) (numeral 7))))))
  · exact ⟨InternalQuotientComparisonProof.orLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · have hn : Nonempty (Derivation body (A.not :: Delta) A.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := tagReject 1 xs hn
    have ht := zeroBranchElim (tagIs 1) (choose (tagIs 2) applicationCase (choose (tagIs 4) ordinaryCase (choose (tagIs 5) numberedCase (choose (tagIs 7) applicationCase (InternalAcceptance.constantZero 19))))) lambdaCase (numeral 1) xs hz (withHyp h A.not)
    obtain ⟨hout⟩ := at2 xs ht
    exact ⟨InternalQuotientComparisonProof.orRight hout⟩

theorem successShape (xs : Fin 19 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (programGraph layer (numeral 1) xs))) :
    Nonempty (Derivation body Delta (eqn (xs 0) (xs 7) ⊓ Targets.active (xs 0))) := by
  have he := equalTags xs h
  have ht := (chooseAccept (eqField 0 7) dispatch (InternalAcceptance.constantZero 19) xs
    (eqAccept 0 7 xs he)).mp h
  exact andIntro he (at1 xs ht)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.LayerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.LayerProof
