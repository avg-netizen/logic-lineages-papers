module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationTerminalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelFinishedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoder OriginalTypedDecoderInternalBranchProof
open OriginalTypedDecoderInternalFuelIterationTerminalProof
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem sameAccepted {n : Nat} (p q yes : Program n) (x y : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p x xs)))
    (hq : Nonempty (Derivation body Delta (programGraph q y xs)))
    (ho : Nonempty (Derivation body Delta
      (programGraph (ifSame p q yes (constant n 0)) (numeral 1) xs))) :
    Nonempty (Derivation body Delta (equal x y ⊓ programGraph yes (numeral 1) xs)) := by
  have h := sameForward p q yes (constant n 0) (numeral 1) x y xs hp hq ho
  apply orCases h
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have hz := constantForward 0 (numeral 1) xs
      (show Nonempty (Derivation body
        (((equal x y).not ⊓ programGraph (constant n 0) (numeral 1) xs) :: Delta)
        (programGraph (constant n 0) (numeral 1) xs)) from
        ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩)
    obtain ⟨hz⟩ := hz
    have hz' : Derivation body
        (((equal x y).not ⊓ programGraph (constant n 0) (numeral 1) xs) :: Delta)
        (eqn (suc z) z) := by simpa only [equalEqn,numeral] using hz
    exact ⟨Derivation.explosion (sucNeZeroApply hz')⟩

theorem finishedSuccess :
    Nonempty (Derivation body Delta (graph1 finished (numeral 1 : OTerm alpha) (numeral 2))) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons (numeral 2) Fin.elim0
  have he1 : Nonempty (Derivation body Delta (equal (numeral 1 : OTerm alpha) (numeral 1))) := by
    rw [equalEqn]; exact ⟨refl (numeral 1)⟩
  have he0 : Nonempty (Derivation body Delta (equal (z : OTerm alpha) z)) := by
    rw [equalEqn]; exact ⟨refl z⟩
  have inner := sameYesIntro work (constant 1 0) (constant 1 1) (constant 1 0)
    (numeral 1) z z xs (pairRight (numeral 2) (numeral 1) z successPair)
    (constantValue 0 xs) he0 (constantValue 1 xs)
  exact sameYesIntro status (constant 1 1) _ (constant 1 0)
    (numeral 1) (numeral 1) (numeral 1) xs
    (pairLeft (numeral 2) (numeral 1) z successPair) (constantValue 1 xs) he1 inner

theorem finishedAcceptedState (state : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 finished (numeral 1) state))) :
    Nonempty (Derivation body Delta (eqn state (numeral 2))) := by
  apply queryCases (![status,work] : Fin 2 → Program 1) (Fin.cons state Fin.elim0) _
  intro beta j ys Theta hj hq
  simp only [InternalTagArithmeticSyntaxProof.eqnRelabel,numeral,sucRelabel,zRelabel]
  have hf' := renameInto hf j Theta hj
  simp only [graph1Rename,oneRename] at hf'
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,
    InternalControlGraphSupportProof.emptyRename] at hq
  let xs : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hs := sameAccepted status (constant 1 1)
    (ifSame work (constant 1 0) (constant 1 1) (constant 1 0))
    (ys 0) (numeral 1) xs (hq 0) (constantValue 1 xs) hf'
  have hw := sameAccepted work (constant 1 0) (constant 1 1)
    (ys 1) z xs (hq 1) (constantValue 0 xs) (andRight hs)
  have es := andLeft hs
  have ew := andLeft hw
  simp only [equalEqn] at es ew
  have hstatus := outputTransport status (ys 0) (numeral 1) xs es (hq 0)
  have hwork := outputTransport work (ys 1) z xs ew (hq 1)
  exact valueUnique InternalPairing.pairing (state.relabel j) (numeral 2)
    (Fin.cons (numeral 1) (Fin.cons z Fin.elim0))
    (InternalApplicationCertificateConstructorsSupportProof.reconstructPair
      (state.relabel j) (numeral 1) z hstatus hwork) successPair

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelFinishedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelFinishedProof
