module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureFuelProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open InternalApplicationResultStackComposition
open InternalApplicationCertifiedResultFoldClosureApplicationCoreProof
open InternalApplicationCertifiedResultFoldClosureBridgeProof
open InternalApplicationCertifiedResultFoldClosureFuelProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof
open InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Internal totality supplies all these constructor witnesses; none is a
new premise of the frozen application target. Coordinates are
[domain,codomain,functionPayload,argumentPayload,arrow,function,argument,
parent,functionOutput,argumentOutput,output]. -/
def functionVisitQ : Program 11 := pairOf (InternalAcceptance.constantZero 11) (.projection 5)
def argumentVisitQ : Program 11 := pairOf (InternalAcceptance.constantZero 11) (.projection 6)
def parentVisitQ : Program 11 := pairOf (InternalAcceptance.constantZero 11) (.projection 7)
def typesQ : Program 11 := pairOf (.projection 0) (.projection 1)
def finishQ : Program 11 := pairOf (InternalLessThan.constantOne 11) (typesQ)
def functionWorkQ : Program 11 := consOf (functionVisitQ) (InternalAcceptance.constantZero 11)
def argumentWorkQ : Program 11 := consOf (argumentVisitQ) (InternalAcceptance.constantZero 11)
def parentWorkQ : Program 11 := consOf (parentVisitQ) (InternalAcceptance.constantZero 11)
def finishWorkQ : Program 11 := consOf (finishQ) (InternalAcceptance.constantZero 11)
def argumentFinishQ : Program 11 := consOf (argumentVisitQ) (finishWorkQ)
def expandedWorkQ : Program 11 := consOf (functionVisitQ) (argumentFinishQ)
def functionResultsQ : Program 11 := consOf (.projection 8) (InternalAcceptance.constantZero 11)
def argumentResultsQ : Program 11 := consOf (.projection 9) (InternalAcceptance.constantZero 11)
def bothResultsQ : Program 11 := consOf (.projection 9) (functionResultsQ)
def outputResultsQ : Program 11 := consOf (.projection 10) (InternalAcceptance.constantZero 11)
def parentStateQ : Program 11 := .composition liveState ![parentWorkQ,InternalAcceptance.constantZero 11]
def expandedStateQ : Program 11 := .composition liveState ![expandedWorkQ,InternalAcceptance.constantZero 11]
def finishStateQ : Program 11 := .composition liveState ![finishWorkQ,bothResultsQ]
def outputStateQ : Program 11 := .composition liveState ![InternalAcceptance.constantZero 11,outputResultsQ]
def payloadQ : Program 11 := .composition InternalUnpair.right (fun _ : Fin 1 => .projection 7)
def queries : Fin 20 → Program 11 :=
  ![functionVisitQ,argumentVisitQ,parentVisitQ,typesQ,finishQ,functionWorkQ,argumentWorkQ,parentWorkQ,finishWorkQ,argumentFinishQ,expandedWorkQ,functionResultsQ,argumentResultsQ,bothResultsQ,outputResultsQ,parentStateQ,expandedStateQ,finishStateQ,outputStateQ,payloadQ]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem applicationFromQueries (guard leaf : Program 1) (combine : Program 4)
    (d e fp ap arrow fn arg parent functionOut argumentOut out : OTerm α)
    (ys : Fin 20 → OTerm α)
    (harrow : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing fn arrow fp)))
    (harg : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing arg d ap)))
    (hparent : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hguard : Nonempty (Derivation body Gamma (graph1 guard (suc z) parent)))
    (hfunction : Nonempty (Derivation body Gamma (certifiedFold guard leaf combine functionOut fn)))
    (hargument : Nonempty (Derivation body Gamma (certifiedFold guard leaf combine argumentOut arg)))
    (hcombine : Nonempty (Derivation body Gamma (graph4 combine out d e functionOut argumentOut)))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (queries i) (ys i)
      (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons arrow (Fin.cons fn (Fin.cons arg (Fin.cons parent (Fin.cons functionOut (Fin.cons argumentOut (Fin.cons out Fin.elim0)))))))))))))) :
    Nonempty (Derivation body Gamma (certifiedFold guard leaf combine out parent)) := by
  let xs : Fin 11 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons arrow (Fin.cons fn (Fin.cons arg (Fin.cons parent (Fin.cons functionOut (Fin.cons argumentOut (Fin.cons out Fin.elim0))))))))))
  have h0 := binaryRecover InternalPairing.pairing (InternalAcceptance.constantZero 11) (.projection 5)
    (ys 0) (z) (fn) xs (hq 0) (constantZeroValue xs) (projectionValue 5 xs)
  have h1 := binaryRecover InternalPairing.pairing (InternalAcceptance.constantZero 11) (.projection 6)
    (ys 1) (z) (arg) xs (hq 1) (constantZeroValue xs) (projectionValue 6 xs)
  have h2 := binaryRecover InternalPairing.pairing (InternalAcceptance.constantZero 11) (.projection 7)
    (ys 2) (z) (parent) xs (hq 2) (constantZeroValue xs) (projectionValue 7 xs)
  have h3 := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 3) (d) (e) xs (hq 3) (projectionValue 0 xs) (projectionValue 1 xs)
  have h4 := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 11) (typesQ)
    (ys 4) (suc z) (ys 3) xs (hq 4) (InternalLessThanSupportProof.oneConstantValue xs) (hq 3)
  have h5 := binaryRecover InternalListCodec.consCode (functionVisitQ) (InternalAcceptance.constantZero 11)
    (ys 5) (ys 0) (z) xs (hq 5) (hq 0) (constantZeroValue xs)
  have h6 := binaryRecover InternalListCodec.consCode (argumentVisitQ) (InternalAcceptance.constantZero 11)
    (ys 6) (ys 1) (z) xs (hq 6) (hq 1) (constantZeroValue xs)
  have h7 := binaryRecover InternalListCodec.consCode (parentVisitQ) (InternalAcceptance.constantZero 11)
    (ys 7) (ys 2) (z) xs (hq 7) (hq 2) (constantZeroValue xs)
  have h8 := binaryRecover InternalListCodec.consCode (finishQ) (InternalAcceptance.constantZero 11)
    (ys 8) (ys 4) (z) xs (hq 8) (hq 4) (constantZeroValue xs)
  have h9 := binaryRecover InternalListCodec.consCode (argumentVisitQ) (finishWorkQ)
    (ys 9) (ys 1) (ys 8) xs (hq 9) (hq 1) (hq 8)
  have h10 := binaryRecover InternalListCodec.consCode (functionVisitQ) (argumentFinishQ)
    (ys 10) (ys 0) (ys 9) xs (hq 10) (hq 0) (hq 9)
  have h11 := binaryRecover InternalListCodec.consCode (.projection 8) (InternalAcceptance.constantZero 11)
    (ys 11) (functionOut) (z) xs (hq 11) (projectionValue 8 xs) (constantZeroValue xs)
  have h12 := binaryRecover InternalListCodec.consCode (.projection 9) (InternalAcceptance.constantZero 11)
    (ys 12) (argumentOut) (z) xs (hq 12) (projectionValue 9 xs) (constantZeroValue xs)
  have h13 := binaryRecover InternalListCodec.consCode (.projection 9) (functionResultsQ)
    (ys 13) (argumentOut) (ys 11) xs (hq 13) (projectionValue 9 xs) (hq 11)
  have h14 := binaryRecover InternalListCodec.consCode (.projection 10) (InternalAcceptance.constantZero 11)
    (ys 14) (out) (z) xs (hq 14) (projectionValue 10 xs) (constantZeroValue xs)
  have h15 := binaryRecover liveState (parentWorkQ) (InternalAcceptance.constantZero 11)
    (ys 15) (ys 7) (z) xs (hq 15) (hq 7) (constantZeroValue xs)
  have h16 := binaryRecover liveState (expandedWorkQ) (InternalAcceptance.constantZero 11)
    (ys 16) (ys 10) (z) xs (hq 16) (hq 10) (constantZeroValue xs)
  have h17 := binaryRecover liveState (finishWorkQ) (bothResultsQ)
    (ys 17) (ys 8) (ys 13) xs (hq 17) (hq 8) (hq 13)
  have h18 := binaryRecover liveState (InternalAcceptance.constantZero 11) (outputResultsQ)
    (ys 18) (z) (ys 14) xs (hq 18) (constantZeroValue xs) (hq 14)
  have hp := unaryRecover InternalUnpair.right (.projection 7) (ys 19) parent xs
    (hq 19) (projectionValue 7 xs)
  obtain ⟨hfiff⟩ := closedApply
    (actualOriginalCertifiedResultFoldRunBridge body guard leaf combine α fn fp (ys 5) functionOut (ys 11))
    (andIntro (pairRight fn arrow fp hfn) (andIntro (visitWorkAt (ys 5) (ys 0) fn h0 h5) h11))
  obtain ⟨haiff⟩ := closedApply
    (actualOriginalCertifiedResultFoldRunBridge body guard leaf combine α arg ap (ys 6) argumentOut (ys 12))
    (andIntro (pairRight arg d ap harg) (andIntro (visitWorkAt (ys 6) (ys 1) arg h1 h6) h12))
  obtain ⟨hfunction⟩ := hfunction
  obtain ⟨hargument⟩ := hargument
  have hrf : Nonempty (Derivation body Gamma
      (actualRun guard leaf combine (payloadFuel fp) (ys 5) z (ys 11))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hfiff) hfunction⟩
  have hra : Nonempty (Derivation body Gamma
      (actualRun guard leaf combine (payloadFuel ap) (ys 6) z (ys 12))) :=
    ⟨Derivation.implicationElimination (Derivation.conjunctionLeft haiff) hargument⟩
  have hshort := applicationRun guard leaf combine d e fp ap arrow fn arg parent
    functionOut argumentOut out (payloadFuel fp) (payloadFuel ap)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
    (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) (ys 10)
    (ys 11) (ys 12) (ys 13) (ys 14) (ys 15) (ys 16) (ys 17) (ys 18)
    harrow hfn harg hparent hguard hcombine
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 hrf hra
  have hbound := applicationFuelBound arrow d e fp ap fn arg parent (ys 19) hparent hp
  obtain ⟨hfull⟩ := runAtBound guard leaf combine
    (suc (OrdinaryArithmetic.addTerm (payloadFuel fp)
      (OrdinaryArithmetic.addTerm (payloadFuel ap) (suc z))))
    (payloadFuel (ys 19)) (ys 7) z (ys 14) hbound hshort
  obtain ⟨hpiff⟩ := closedApply
    (actualOriginalCertifiedResultFoldRunBridge body guard leaf combine α parent (ys 19) (ys 7) out (ys 14))
    (andIntro hp (andIntro (visitWorkAt (ys 7) (ys 2) parent h2 h7) h14))
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hpiff) hfull⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationQueryProof
