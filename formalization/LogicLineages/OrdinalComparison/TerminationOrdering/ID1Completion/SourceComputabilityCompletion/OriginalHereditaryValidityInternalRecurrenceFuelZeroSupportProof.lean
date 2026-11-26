module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelZeroSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalListCodecDecompositionSupportProof InternalListCodecSupportProof
open OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def payloadOfFrame : Program 1 := rightOf (leftOf (.projection 0))

 theorem framePayloadValue (frame payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 payloadOfFrame payload frame))) :
    Nonempty (Derivation body Delta (graph1 frameFuel (suc payload) frame)) :=
  unaryValue .succ payloadOfFrame (suc payload) payload (Fin.cons frame Fin.elim0)
    (InternalControlGraphSupportProof.successorValue (Fin.cons payload Fin.elim0)) hp

 theorem nonemptyPositive (code frame rest count : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (WorkCons code frame rest)))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph count code))) :
    Nonempty (Derivation body Delta (eqn count z).not) := by
  let qs : Fin 2 → Program 2 := ![
    .composition payloadOfFrame (fun _ : Fin 1 => .projection 0),
    .composition workFuel (fun _ : Fin 1 => .projection 1)]
  let xs : Fin 2 → OTerm alpha := Fin.cons frame (Fin.cons rest Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [nonzeroRename]
  simp only [xs,consTermRename,emptyRename] at hq
  have hc' := renameInto hc j Theta hj
  simp only [WorkCons,graph2Rename] at hc'
  have hf' := renameInto hf j Theta hj
  rw [fuelRename] at hf'
  let xx : Fin 2 → OTerm beta := Fin.cons (frame.relabel j) (Fin.cons (rest.relabel j) Fin.elim0)
  have hp := unaryRecover payloadOfFrame (.projection 0) (ys 0) (frame.relabel j)
    xx (hq 0) (projectionValue 0 xx)
  have ht := unaryRecover workFuel (.projection 1) (ys 1) (rest.relabel j)
    xx (hq 1) (projectionValue 1 xx)
  obtain ⟨he⟩ := consRecover (code.relabel j) (frame.relabel j) (rest.relabel j)
    (suc (ys 0)) (ys 1) (count.relabel j) hc'
    (framePayloadValue (frame.relabel j) (ys 0) hp) ht hf'
  have hs := trans he (leftSuccessor (ys 0) (ys 1))
  have hz : Derivation body (eqn (count.relabel j) z :: Theta)
      (eqn (count.relabel j) z) := Derivation.hypothesis List.mem_cons_self
  exact ⟨Derivation.implicationIntroduction
    (sucNeZeroApply (trans (symm (InternalBetaTotalityProof.addHyp hs _)) hz))⟩

 theorem nonzeroPositive (count code : OTerm alpha)
    (hn : Nonempty (Derivation body Delta (eqn code z).not))
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph count code))) :
    Nonempty (Derivation body Delta (eqn count z).not) := by
  let qs : Fin 2 → Program 1 := ![InternalListCodec.headCode,InternalListCodec.tailCode]
  apply queryCases qs (Fin.cons code Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [nonzeroRename]
  simp only [consTermRename,emptyRename] at hq
  have hn' := renameInto hn j Theta hj
  rw [nonzeroRename] at hn'
  have hf' := renameInto hf j Theta hj
  rw [fuelRename] at hf'
  have hc := reconstructNonzero (code.relabel j) (ys 0) (ys 1) hn' (hq 0) (hq 1)
  exact nonemptyPositive (code.relabel j) (ys 0) (ys 1) (count.relabel j) hc hf'

 theorem zeroReflect (count code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph count code)))
    (hz : Nonempty (Derivation body Delta (eqn count z))) :
    Nonempty (Derivation body Delta (eqn code z)) := by
  apply InternalOriginalPairingOrderArithmeticProof.formulaCases (eqn code z)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · obtain ⟨hn⟩ := nonzeroPositive count code
      (show Nonempty (Derivation body ((eqn code z).not :: Delta) (eqn code z).not) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hf _)
    obtain ⟨hz'⟩ := withHyp hz (eqn code z).not
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn hz')⟩

 theorem zeroPreserve (count code : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (WorkFuelGraph count code)))
    (hz : Nonempty (Derivation body Delta (eqn code z))) :
    Nonempty (Derivation body Delta (eqn count z)) :=
  nilRecover count (headTransport workFuel count code z Fin.elim0 hz hf)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelZeroSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelZeroSupportProof
