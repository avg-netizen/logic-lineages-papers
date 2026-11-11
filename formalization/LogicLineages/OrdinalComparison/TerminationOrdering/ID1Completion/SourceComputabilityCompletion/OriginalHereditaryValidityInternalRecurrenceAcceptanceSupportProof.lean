module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalNodeSupportProof OriginalHereditaryValidityInternalStateSupportProof
open OriginalHereditaryValidityInternalRecurrenceIterationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem stateFrameLive (state workCode frame raw parameter restCode : OTerm alpha)
    (h : Nonempty (Derivation body Gamma
      (StateFrame state workCode frame raw parameter restCode))) :
    Nonempty (Derivation body Gamma (LiveWork state)) := by
  have hs := andLeft h
  have hw := andLeft (andRight h)
  have hp := pairRight state (numeral 1) workCode hs
  have hn := andRight (andRight (InternalListCodecSupportProof.consDestruction
    workCode frame restCode hw))
  let A := graph1 work z state
  have he := valueUnique work workCode z (Fin.cons state Fin.elim0)
    (weakenProof hp (fun q hq => List.mem_cons_of_mem A hq))
    (show Nonempty (Derivation body (A :: Gamma) A) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hn⟩ := weakenProof hn (fun q hq => List.mem_cons_of_mem A hq)
  obtain ⟨he⟩ := he
  exact andIntro (pairLeft state (numeral 1) workCode hs)
    ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn he)⟩

/-- Initial liveness is derived from the ORIGINAL singleton construction.
Neither its frame/work codes nor their nonzeroness is an external premise. -/
theorem initialLive (state raw parameter : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (graph2 initial state raw parameter))) :
    Nonempty (Derivation body Gamma (LiveWork state)) := by
  let frame : Program 2 := pairOf (.projection 0) (.projection 1)
  let workCode : Program 2 := consOf frame (InternalAcceptance.constantZero 2)
  let qs : Fin 2 → Program 2 := ![frame,workCode]
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Delta hj hq
  rw [liveWorkRename]
  have h' := renameInto h j Delta hj
  rw [graph2Rename] at h'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel j)
    (Fin.cons (parameter.relabel j) Fin.elim0)
  have hf := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) (raw.relabel j) (parameter.relabel j) xx (hq 0)
    (projectionValue 0 xx) (projectionValue 1 xx)
  have hw := binaryRecover InternalListCodec.consCode frame (InternalAcceptance.constantZero 2)
    (ys 1) (ys 0) z xx (hq 1) (hq 0)
    (InternalLessThanSupportProof.zeroConstantValue xx)
  have hs := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) workCode
    (state.relabel j) (numeral 1) (ys 1) xx h'
    (InternalLessThanSupportProof.oneConstantValue xx) (hq 1)
  exact stateFrameLive (state.relabel j) (ys 1) (ys 0)
    (raw.relabel j) (parameter.relabel j) z (andIntro hs (andIntro hw hf))

theorem fuelAtPayload (raw parameter payload : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw))) :
    Nonempty (Derivation body Gamma (graph2 fuel (suc payload) raw parameter)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have hraw := unaryValue InternalUnpair.right (.projection 0) payload raw xs hp
    (projectionValue 0 xs)
  exact unaryValue .succ (rightOf (.projection 0)) (suc payload) payload xs
    (successorValue (Fin.cons payload Fin.elim0)) hraw

/-- One rejected original root consumes the first unit of the ACTUAL
payload+1 bound. Failure absorption pays every remaining symbolic unit. -/
theorem rejectedInitialRun (s t m : Program 2) (state raw parameter payload : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma (graph2 initial state raw parameter)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw)))
    (hn : Nonempty (Derivation body Gamma
      (graph1 (nodeCheck s t m) (numeral 1) state).not)) :
    Nonempty (Derivation body Gamma (graph2 (run s t m) z raw parameter)) := by
  have hf := OriginalHereditaryValidityInternalRejectSupportProof.rejectNode
    s t m state (initialLive state raw parameter hi) hn
  have hr := rejectingFirstIterate s t m payload state hf
  exact binaryValue (iterate s t m) fuel initial z (suc payload) state
    (Fin.cons raw (Fin.cons parameter Fin.elim0)) hr (fuelAtPayload raw parameter payload hp) hi

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceSupportProof
