module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeZeroPrefixCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeZeroPrefixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalApplicationStepPeelSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalNumericListSortExchange

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem extend (source target certificate payloadCode newFront newCertificate newSource newTarget : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph3 edge (suc z) source target certificate)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing certificate z payloadCode)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newCertificate newFront payloadCode)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append newSource newFront source)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append newTarget newFront target)))
 : Nonempty (Derivation body Delta (graph3 edge (suc z) newSource newTarget newCertificate)) := by
 let qs : Fin 8 → Program 3 := ![first,rest,second,tail,afterSecond,afterFirst,firstSecond,secondFirst]
 let xs : Fin 3 → OTerm alpha := Fin.cons source (Fin.cons target (Fin.cons certificate Fin.elim0))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta rho v Theta hrho hq
 simp only [graph3Rename,sucRelabel,zRelabel]
 have hv : (fun i => (xs i).relabel rho) = Fin.cons (source.relabel rho)
   (Fin.cons (target.relabel rho) (Fin.cons (certificate.relabel rho) Fin.elim0)) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hv] at hq
 have he' := renameInto he rho Theta hrho
 simp only [graph3Rename,graph2Rename,sucRelabel,zRelabel] at he'
 have hp' := renameInto hp rho Theta hrho
 simp only [graph3Rename,graph2Rename,sucRelabel,zRelabel] at hp'
 have hn' := renameInto hn rho Theta hrho
 simp only [graph3Rename,graph2Rename,sucRelabel,zRelabel] at hn'
 have hs' := renameInto hs rho Theta hrho
 simp only [graph3Rename,graph2Rename,sucRelabel,zRelabel] at hs'
 have ht' := renameInto ht rho Theta hrho
 simp only [graph3Rename,graph2Rename,sucRelabel,zRelabel] at ht'
 exact OriginalNumericListSortExchangeZeroPrefixCoreProof.atValues (source.relabel rho) (target.relabel rho) (certificate.relabel rho) (payloadCode.relabel rho) (newFront.relabel rho) (newCertificate.relabel rho) (newSource.relabel rho) (newTarget.relabel rho) v he' hp' hn' hs' ht' hq
theorem actualZeroPrefix : OriginalNumericListSortExchangeZeroPrefixTargets.ActualZeroPrefix := by
 intro body alpha Delta source target certificate payloadCode newFront newCertificate newSource newTarget he hp hn hs ht
 exact extend source target certificate payloadCode newFront newCertificate newSource newTarget he hp hn hs ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeZeroPrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortExchangeZeroPrefixProof
