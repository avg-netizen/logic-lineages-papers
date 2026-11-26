module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalHereditaryObservationLayer
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem pairComponents (P Q : Program 2) (input parameter out a b : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out a b)))
    (hr : Nonempty (Derivation body Delta (graph2 (pairOf P Q) out input parameter))) :
    Nonempty (Derivation body Delta (graph2 P a input parameter ⊓ graph2 Q b input parameter)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  apply queryCases (![P,Q] : Fin 2 → Program 2) xs _
  intro beta j ys Theta hj hq
  simp only [InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph2Rename]
  let xx : Fin 2 → OTerm beta := Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have he : (fun i => (xs i).relabel j) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [he] at hq
  have hp' := renameInto hp j Theta hj
  rw [graph2Rename] at hp'
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hr'
  have hactual := binaryRecover InternalPairing.pairing P Q (out.relabel j) (ys 0) (ys 1) xx hr' (hq 0) (hq 1)
  have ha := valueUnique InternalUnpair.left (ys 0) (a.relabel j) (Fin.cons (out.relabel j) Fin.elim0)
    (pairLeft (out.relabel j) (ys 0) (ys 1) hactual) (pairLeft (out.relabel j) (a.relabel j) (b.relabel j) hp')
  have hb := valueUnique InternalUnpair.right (ys 1) (b.relabel j) (Fin.cons (out.relabel j) Fin.elim0)
    (pairRight (out.relabel j) (ys 0) (ys 1) hactual) (pairRight (out.relabel j) (a.relabel j) (b.relabel j) hp')
  exact andIntro (outputTransport P (ys 0) (a.relabel j) xx ha (hq 0))
    (outputTransport Q (ys 1) (b.relabel j) xx hb (hq 1))

theorem assembly (R Q : Program 2) (input parameter out inner a b c : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out a inner)))
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner b c)))
    (ha : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) a input parameter)))
    (hb : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) b input parameter)))
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryDeletionRows.rows Q) c input parameter))) :
    Nonempty (Derivation body Delta (graph2 (layer R Q) out input parameter)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  have hinner := binaryValue InternalPairing.pairing (OriginalRootObservation.rootObservation Q)
    (OriginalHereditaryDeletionRows.rows Q) inner b c xs hi hb hc
  exact binaryValue InternalPairing.pairing (OriginalRootObservation.rootObservation R)
    (pairOf (OriginalRootObservation.rootObservation Q) (OriginalHereditaryDeletionRows.rows Q))
    out a inner xs ho ha hinner

theorem recovery (R Q : Program 2) (input parameter out inner a b c : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out a inner)))
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner b c)))
    (hr : Nonempty (Derivation body Delta (graph2 (layer R Q) out input parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalRootObservation.rootObservation R) a input parameter ⊓
        (graph2 (OriginalRootObservation.rootObservation Q) b input parameter ⊓
          graph2 (OriginalHereditaryDeletionRows.rows Q) c input parameter))) := by
  have hout := pairComponents (OriginalRootObservation.rootObservation R)
    (pairOf (OriginalRootObservation.rootObservation Q) (OriginalHereditaryDeletionRows.rows Q))
    input parameter out a inner ho hr
  exact andIntro (andLeft hout)
    (pairComponents (OriginalRootObservation.rootObservation Q) (OriginalHereditaryDeletionRows.rows Q)
      input parameter inner b c hi (andRight hout))

theorem actualInternal : OriginalHereditaryObservationLayerTargets.Internal := by
  intro R Q body alpha Delta input parameter out inner a b c
  let A := graph2 InternalPairing.pairing out a inner ⊓ graph2 InternalPairing.pairing inner b c
  let B := graph2 (layer R Q) out input parameter
  let C := graph2 (OriginalRootObservation.rootObservation R) a input parameter ⊓
    (graph2 (OriginalRootObservation.rootObservation Q) b input parameter ⊓
      graph2 (OriginalHereditaryDeletionRows.rows Q) c input parameter)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := recovery R Q input parameter out inner a b c
    (withHyp (andLeft h) B) (withHyp (andRight h) B)
    (show Nonempty (Derivation body (B :: A :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hc : Nonempty (Derivation body (C :: A :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := assembly R Q input parameter out inner a b c
    (withHyp (andLeft h) C) (withHyp (andRight h) C)
    (andLeft hc) (andLeft (andRight hc)) (andRight (andRight hc))
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerInternalProof
