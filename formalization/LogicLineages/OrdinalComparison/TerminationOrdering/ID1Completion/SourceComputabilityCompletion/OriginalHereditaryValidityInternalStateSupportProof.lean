module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem stateFrameRename {beta : Type}
    (state workCode frame raw parameter restCode : OTerm alpha) (j : alpha → beta) :
    (StateFrame state workCode frame raw parameter restCode).relabel j =
      StateFrame (state.relabel j) (workCode.relabel j) (frame.relabel j)
        (raw.relabel j) (parameter.relabel j) (restCode.relabel j) := by
  simp only [StateFrame,StateGraph,WorkCons,FrameGraph,conjunctionRename,graph2Rename,oneRename]

@[simp] theorem liveWorkRename {beta : Type} (state : OTerm alpha) (j : alpha → beta) :
    (LiveWork state).relabel j = LiveWork (state.relabel j) := by
  change (graph1 status (numeral 1) state).relabel j ⊓
    ((graph1 work OrdinaryArithmetic.zeroTerm state).relabel j).not = _
  rw [graph1Rename,graph1Rename,oneRename,InternalTagArithmeticSyntaxProof.zRelabel]
  rfl

/-- Failure of the zero-output graph forces the SAME actual output nonzero.
This is graph functionality/equality transport, not native evaluation. -/
theorem nonzeroOfNotZeroGraph {n : Nat} (p : Program n) (out : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph p out xs)))
    (hn : Nonempty (Derivation body Delta (programGraph p OrdinaryArithmetic.zeroTerm xs).not)) :
    Nonempty (Derivation body Delta (equal out OrdinaryArithmetic.zeroTerm).not) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hn⟩ := hn
  let A := equal out OrdinaryArithmetic.zeroTerm
  have he : Nonempty (Derivation body (A :: Delta)
      (InternalTagArithmeticSyntaxProof.eqn out OrdinaryArithmetic.zeroTerm)) := by
    simpa only [A,equalEqn] using
      (show Nonempty (Derivation body (A :: Delta) A) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hz⟩ := outputTransport p out OrdinaryArithmetic.zeroTerm xs he
    (show Nonempty (Derivation body (A :: Delta) (programGraph p out xs)) from
      ⟨InternalBetaTotalityProof.addHyp hp A⟩)
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn A) hz)⟩

/-- Original pair/cons destruction supplies all selectors of one connected
live frame, with the original raw/parameter and unmodified tail. -/
theorem stateFrameOpened (state workCode frame raw parameter restCode : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (StateFrame state workCode frame raw parameter restCode))) :
    Nonempty (Derivation body Delta
      (OpenedWork state workCode frame raw parameter restCode)) := by
  have hs := andLeft h
  have hw := andLeft (andRight h)
  have hf := andRight (andRight h)
  have hwork := pairRight state (numeral 1) workCode hs
  have hc := InternalListCodecSupportProof.consDestruction workCode frame restCode hw
  have hhead := andLeft hc
  have htail := andLeft (andRight hc)
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hframe := unaryValue InternalListCodec.headCode work frame workCode xs hhead hwork
  have hrest := unaryValue InternalListCodec.tailCode work restCode workCode xs htail hwork
  have hraw := unaryValue InternalUnpair.left currentFrame raw frame xs
    (pairLeft frame raw parameter hf) hframe
  have hparameter := unaryValue InternalUnpair.right currentFrame parameter frame xs
    (pairRight frame raw parameter hf) hframe
  exact andIntro h (andIntro hwork (andIntro hframe
    (andIntro hraw (andIntro hparameter hrest))))

/-- The original singleton constructor exposes its SAME supplied inputs;
its internal frame and cons codes are supplied by Program totality. -/
theorem initialSelectors (state raw parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 initial state raw parameter))) :
    Nonempty (Derivation body Delta
      (graph1 currentRaw raw state ⊓ graph1 currentParameter parameter state)) := by
  let frame : Program 2 := pairOf (.projection 0) (.projection 1)
  let workCode : Program 2 := consOf frame (InternalAcceptance.constantZero 2)
  let qs : Fin 2 → Program 2 := ![frame,workCode]
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  change Nonempty (Derivation body Theta
    ((graph1 currentRaw raw state).relabel j ⊓
      (graph1 currentParameter parameter state).relabel j))
  rw [graph1Rename,graph1Rename]
  have h' := renameInto h j Theta hj
  rw [graph2Rename] at h'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel j)
    (Fin.cons (parameter.relabel j) Fin.elim0)
  have hf := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) (raw.relabel j) (parameter.relabel j) xx (hq 0)
    (projectionValue 0 xx) (projectionValue 1 xx)
  have hw := binaryRecover InternalListCodec.consCode frame (InternalAcceptance.constantZero 2)
    (ys 1) (ys 0) OrdinaryArithmetic.zeroTerm xx (hq 1) (hq 0)
    (InternalLessThanSupportProof.zeroConstantValue xx)
  have hs := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) workCode
    (state.relabel j) (numeral 1) (ys 1) xx h'
    (InternalLessThanSupportProof.oneConstantValue xx) (hq 1)
  have ho := stateFrameOpened (state.relabel j) (ys 1) (ys 0)
    (raw.relabel j) (parameter.relabel j) OrdinaryArithmetic.zeroTerm
    (andIntro hs (andIntro hw hf))
  exact andIntro (andLeft (andRight (andRight (andRight ho))))
    (andLeft (andRight (andRight (andRight (andRight ho)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateSupportProof
