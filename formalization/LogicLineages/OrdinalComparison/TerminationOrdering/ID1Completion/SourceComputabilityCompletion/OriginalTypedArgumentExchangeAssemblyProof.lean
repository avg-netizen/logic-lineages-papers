module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeRawCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixAdjacentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeAssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionClosureLogicProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentExchange OriginalTypedArgumentExchangeRawProof OriginalTypedArgumentExchangeRawCasesProof OriginalTypedArgumentObservations
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atLocal (R : Program 2) (source target certificate parameter observedSource observedTarget numericCertificate : OTerm alpha)
 (v : Fin 14 → OTerm alpha) (w : Fin 8 → OTerm alpha) (localSource localTarget localCertificate : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (facts source target certificate v)))
 (hm : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentPrefixBuilder.mapped R) (w 0) (v 0) parameter)))
 (hq : Nonempty (Derivation body Delta (graph2 R (w 1) (v 1) parameter)))
 (hr : Nonempty (Derivation body Delta (graph2 R (w 2) (v 2) parameter)))
 (htq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (w 3) (v 4) (w 1))))
 (htr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (w 4) (v 6) (w 2))))
 (htail : Nonempty (Derivation body Delta (graph2 (argumentObservations R) (w 5) (v 3) parameter)))
 (hrest : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (w 6) (w 4) (w 5))))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (w 7) (w 3) (w 6))))
 (hcert : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing numericCertificate (w 0) (w 7))))
 (hsource : Nonempty (Derivation body Delta (graph2 (argumentObservations R) observedSource source parameter)))
 (htarget : Nonempty (Derivation body Delta (graph2 (argumentObservations R) observedTarget target parameter)))
 (hls : Nonempty (Derivation body Delta (graph2 (argumentObservations R) localSource (v 10) parameter)))
 (hlt : Nonempty (Derivation body Delta (graph2 (argumentObservations R) localTarget (v 11) parameter)))
 (hlc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing localCertificate z (w 7)))) :
 Nonempty (Derivation body Delta (graph3 OriginalNumericListSortExchange.edge (suc z) observedSource observedTarget numericCertificate)) := by
 have f1 := andRight hf
 have f2 := andRight f1
 have f3 := andRight f2
 have f4 := andRight f3
 have f5 := andRight f4
 have f6 := andRight f5
 exact OriginalTypedArgumentPrefixAdjacentProof.actualAdjacent R body alpha Delta
   (v 4) (v 6) (v 5) (v 7) (v 3) (v 8) (v 9) (v 10) (v 11) (v 1) (v 2)
   (w 1) (w 2) (w 3) (w 4) parameter (w 5) localSource localTarget (w 6) (w 7) localCertificate
   (v 0) (w 0) source target observedSource observedTarget numericCertificate
   (andLeft f5)
   (andIntro (andLeft f3) (andIntro (andLeft f4) (andIntro hq (andIntro hr (andIntro htq htr)))))
   (andIntro htail (andIntro hls hlt)) (andIntro hrest (andIntro hpay hlc))
   (andLeft f6) (andRight f6) hm hsource htarget hcert
theorem atTranslated (R : Program 2) (source target certificate parameter observedSource observedTarget numericCertificate : OTerm alpha)
 (v : Fin 14 → OTerm alpha) (w : Fin 8 → OTerm alpha)
 (hf : Nonempty (Derivation body Delta (facts source target certificate v)))
 (hm : Nonempty (Derivation body Delta (graph2 (OriginalTypedArgumentPrefixBuilder.mapped R) (w 0) (v 0) parameter)))
 (hq : Nonempty (Derivation body Delta (graph2 R (w 1) (v 1) parameter)))
 (hr : Nonempty (Derivation body Delta (graph2 R (w 2) (v 2) parameter)))
 (htq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (w 3) (v 4) (w 1))))
 (htr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (w 4) (v 6) (w 2))))
 (htail : Nonempty (Derivation body Delta (graph2 (argumentObservations R) (w 5) (v 3) parameter)))
 (hrest : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (w 6) (w 4) (w 5))))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (w 7) (w 3) (w 6))))
 (hcert : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing numericCertificate (w 0) (w 7))))
 (hsource : Nonempty (Derivation body Delta (graph2 (argumentObservations R) observedSource source parameter)))
 (htarget : Nonempty (Derivation body Delta (graph2 (argumentObservations R) observedTarget target parameter)))
 : Nonempty (Derivation body Delta (graph3 OriginalNumericListSortExchange.edge (suc z) observedSource observedTarget numericCertificate)) := by
 let qs : Fin 3 → Program 4 := ![
   .composition (argumentObservations R) ![.projection 0,.projection 2],
   .composition (argumentObservations R) ![.projection 1,.projection 2],
   pairOf (OriginalRawSyntaxTransport.constant 4 0) (.projection 3)]
 let xs : Fin 4 → OTerm alpha := ![v 10,v 11,parameter,w 7]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta rho values Theta hrho hvals
 simp only [graph3Rename,sucRelabel,zRelabel]
 let ys : Fin 4 → OTerm beta := ![(v 10).relabel rho,(v 11).relabel rho,parameter.relabel rho,(w 7).relabel rho]
 have hxs : (fun i => (xs i).relabel rho) = ys := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
 rw [hxs] at hvals
 have q0 : Nonempty (Derivation body Theta (programGraph (.composition (argumentObservations R) ![.projection 0,.projection 2]) (values 0) ys)) := hvals 0
 have q1 : Nonempty (Derivation body Theta (programGraph (.composition (argumentObservations R) ![.projection 1,.projection 2]) (values 1) ys)) := hvals 1
 have q2 : Nonempty (Derivation body Theta (programGraph (pairOf (OriginalRawSyntaxTransport.constant 4 0) (.projection 3)) (values 2) ys)) := hvals 2
 have hls := binaryRecover (argumentObservations R) (.projection 0) (.projection 2) (values 0) ((v 10).relabel rho) (parameter.relabel rho) ys q0 (projectionValue 0 ys) (projectionValue 2 ys)
 have hlt := binaryRecover (argumentObservations R) (.projection 1) (.projection 2) (values 1) ((v 11).relabel rho) (parameter.relabel rho) ys q1 (projectionValue 1 ys) (projectionValue 2 ys)
 have hlc := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 4 0) (.projection 3)
   (values 2) z ((w 7).relabel rho) ys q2 (InternalAcceptanceConjunctionProof.constantZeroValue ys) (projectionValue 3 ys)
 have hf' := renameInto hf rho Theta hrho
 rw [factsRename] at hf'
 have hm' := renameInto hm rho Theta hrho
 rw [graph2Rename] at hm'
 have hq' := renameInto hq rho Theta hrho
 rw [graph2Rename] at hq'
 have hr' := renameInto hr rho Theta hrho
 rw [graph2Rename] at hr'
 have htq' := renameInto htq rho Theta hrho
 rw [graph2Rename] at htq'
 have htr' := renameInto htr rho Theta hrho
 rw [graph2Rename] at htr'
 have htail' := renameInto htail rho Theta hrho
 rw [graph2Rename] at htail'
 have hrest' := renameInto hrest rho Theta hrho
 rw [graph2Rename] at hrest'
 have hpay' := renameInto hpay rho Theta hrho
 rw [graph2Rename] at hpay'
 have hcert' := renameInto hcert rho Theta hrho
 rw [graph2Rename] at hcert'
 have hsource' := renameInto hsource rho Theta hrho
 rw [graph2Rename] at hsource'
 have htarget' := renameInto htarget rho Theta hrho
 rw [graph2Rename] at htarget'
 exact atLocal R (source.relabel rho) (target.relabel rho) (certificate.relabel rho) (parameter.relabel rho) (observedSource.relabel rho) (observedTarget.relabel rho) (numericCertificate.relabel rho)
   (fun i => (v i).relabel rho) (fun i => (w i).relabel rho) (values 0) (values 1) (values 2)
   hf' hm' hq' hr' htq' htr' htail' hrest' hpay' hcert' hsource' htarget' hls hlt hlc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeAssemblyProof
