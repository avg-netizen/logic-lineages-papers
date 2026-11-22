module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenBaseProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (recursionZeroValue valueUnique outputTransport headTransport)
open ID1Completion.InternalPairing (pairing)
open ID1Completion.InternalPairingSupportProof (pairingOfLess)
open ID1Completion.InternalUnpair (left right)
open ID1Completion.InternalUnpairProof (actualOriginalGeneratedCodeInverse)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open ID1Completion.InternalTagArithmeticSupportProof (trans refl)
open ID1Completion.InternalAdditionLawsProof (add addZero leftZero)
open ID1Completion.InternalMultiplicationLawsProof (mul mulSucc mulZero congAddRight)
open ID1Completion.InternalQuotientComparisonProof (equalToNext)
open ID1Completion.InternalApplicationValidityStackAppendTransitionProof (pairZero)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverGrammarStageTargets (initialLayer)
open NumberedWindowInternalCoverSelectedGrammarTargets
open NumberedWindowInternalCoverSelectedGrammarOpenTargets
open NumberedWindowInternalCoverSelectedGrammarOpenRowProof (alignStageTape)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The original base pair is [0,1], not the opposite [1,0].
Prove its actual ordinary graph with the original less branch. -/
private theorem basePair :
    Nonempty (Derivation body Γ (programGraph pairing (suc (z : OTerm α))
      (Fin.cons z (Fin.cons (suc z) Fin.elim0)))) := by
  let one : OTerm α := suc z
  have less := equalToNext (body := body) (Gamma := Γ) (refl (z : OTerm α))
  have raw := pairingOfLess z one ⟨less⟩
  have mulOne : Derivation body Γ (eqn (mul one one) one) :=
    trans (mulSucc one z) (trans (congAddRight one (mulZero one)) (leftZero one))
  exact outputTransport pairing (add (mul one one) z) one
    (Fin.cons z (Fin.cons one Fin.elim0)) ⟨trans (addZero _) mulOne⟩ raw

private theorem baseCode (H K M : OTerm α) :
    Nonempty (Derivation body Γ (grammarReport (suc z) z H K M)) := by
  have base : Nonempty (Derivation body Γ (programGraph initialLayer (suc z) ![H,K,M])) := by
    change Nonempty (Derivation body Γ (programGraph (literal 3 1) (numeral 1) ![H,K,M]))
    exact literalGraph 1 ![H,K,M]
  rw [grammarReport,alignStageTape]
  exact recursionZeroValue initialLayer selectedGrammarRow (suc z) ![H,K,M] base

theorem exact_OpenSelectedGrammarBaseSplit : ExactOpenSelectedGrammarBaseSplit := by
  intro body α Γ state terms args H K M run tRead aRead
  have same := valueUnique selectedGrammar (suc z) state (grammarTape z H K M)
    (baseCode H K M) run
  obtain ⟨inverse⟩ := actualOriginalGeneratedCodeInverse body α (suc z) z (suc z)
  obtain ⟨paired⟩ := basePair (body := body) (α := α) (Γ := Γ)
  have both := Derivation.implicationElimination (weakenClosed inverse Γ) paired
  have readT := headTransport left z (suc z) state Fin.elim0 same ⟨Derivation.conjunctionLeft both⟩
  have readA := headTransport right (suc z) (suc z) state Fin.elim0 same ⟨Derivation.conjunctionRight both⟩
  have oneTape : (Fin.cons state Fin.elim0 : Fin 1 → OTerm α) = ![state] := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  rw [oneTape] at readT readA
  obtain ⟨termEq⟩ := valueUnique left z terms ![state] readT tRead
  obtain ⟨argsEq⟩ := valueUnique right (suc z) args ![state] readA aRead
  have singleton := consValue (body := body) (Gamma := Γ) z z z pairZero
  obtain ⟨argsCons⟩ := outputTransport consCode (suc z) args
    (Fin.cons z (Fin.cons z Fin.elim0)) ⟨argsEq⟩ singleton
  exact ⟨Derivation.conjunctionIntroduction termEq (Derivation.conjunctionIntroduction argsEq argsCons)⟩

#print axioms exact_OpenSelectedGrammarBaseSplit

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenBaseProof
