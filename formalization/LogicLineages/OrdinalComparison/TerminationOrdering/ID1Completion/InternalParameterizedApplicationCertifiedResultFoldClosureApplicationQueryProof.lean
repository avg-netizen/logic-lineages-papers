module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureBridgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureFuelProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open InternalApplicationResultStackComposition (liveState)
open InternalParameterizedApplicationResultStackCompositionSyntaxProof
open InternalApplicationCertifiedResultFoldClosureApplicationQueryProof
open InternalApplicationCertifiedResultFoldClosureApplicationCoreProof (visitWorkAt)
open InternalParameterizedApplicationCertifiedResultFoldClosure
open InternalParameterizedApplicationCertifiedResultFoldClosureApplicationCoreProof
open InternalParameterizedApplicationCertifiedResultFoldClosureBridgeProof
open InternalApplicationCertifiedResultFoldClosureFuelProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof
open InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem applicationFromQueries (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α)
    (d e fp ap arrow fn arg parent functionOut argumentOut out : OTerm α)
    (ys : Fin 20 → OTerm α)
    (harrow : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing fn arrow fp)))
    (harg : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing arg d ap)))
    (hparent : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hguard : Nonempty (Derivation body Gamma (graph2 guard (suc z) parent parameter)))
    (hfunction : Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine functionOut fn parameter)))
    (hargument : Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine argumentOut arg parameter)))
    (hcombine : Nonempty (Derivation body Gamma (programGraph combine out (Fin.cons d (Fin.cons e (Fin.cons functionOut (Fin.cons argumentOut (Fin.cons parameter Fin.elim0))))))))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (queries i) (ys i)
      (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons arrow (Fin.cons fn (Fin.cons arg (Fin.cons parent (Fin.cons functionOut (Fin.cons argumentOut (Fin.cons out Fin.elim0)))))))))))))) :
    Nonempty (Derivation body Gamma (certifiedFoldP guard leaf combine out parent parameter)) := by
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
  have hrf := runOfCertifiedFold guard leaf combine fn fp (ys 5) functionOut (ys 11) parameter
    (pairRight fn arrow fp hfn) (visitWorkAt (ys 5) (ys 0) fn h0 h5) h11 hfunction
  have hra := runOfCertifiedFold guard leaf combine arg ap (ys 6) argumentOut (ys 12) parameter
    (pairRight arg d ap harg) (visitWorkAt (ys 6) (ys 1) arg h1 h6) h12 hargument
  have hshort := applicationRun guard leaf combine parameter d e fp ap arrow fn arg parent
    functionOut argumentOut out (payloadFuel fp) (payloadFuel ap)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
    (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) (ys 10)
    (ys 11) (ys 12) (ys 13) (ys 14) (ys 15) (ys 16) (ys 17) (ys 18)
    harrow hfn harg hparent hguard hcombine
    h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 hrf hra
  have hbound := applicationFuelBound arrow d e fp ap fn arg parent (ys 19) hparent hp
  obtain ⟨hfull⟩ := InternalParameterizedApplicationCertifiedResultFoldClosureApplicationCoreProof.runAtBound guard leaf combine parameter
    (suc (OrdinaryArithmetic.addTerm (payloadFuel fp)
      (OrdinaryArithmetic.addTerm (payloadFuel ap) (suc z))))
    (payloadFuel (ys 19)) (ys 7) z (ys 14) hbound hshort
  exact certifiedFoldOfRun guard leaf combine parent (ys 19) (ys 7) out (ys 14) parameter
    hp (visitWorkAt (ys 7) (ys 2) parent h2 h7) h14 ⟨hfull⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationQueryProof
