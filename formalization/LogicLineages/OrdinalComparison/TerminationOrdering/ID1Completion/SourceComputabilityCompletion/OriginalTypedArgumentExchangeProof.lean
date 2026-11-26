module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeAssemblyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeTranslationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalTypedArgumentExchange OriginalTypedArgumentExchangeRawProof OriginalTypedArgumentExchangeRawCasesProof OriginalTypedArgumentExchangeTranslationProof
open OriginalTypedArgumentExchangeAssemblyProof

theorem actualTranslation : OriginalTypedArgumentExchangeTargets.ActualTranslation := by
 intro R body alpha Delta source target certificate parameter observedSource observedTarget numericCertificate he hs ht hn
 apply rawCases source target certificate _ he
 intro beta rho Theta v hrho hf
 simp only [graph3Rename,sucRelabel,zRelabel]
 have hs' := renameInto hs rho Theta hrho
 have ht' := renameInto ht rho Theta hrho
 have hn' := renameInto hn rho Theta hrho
 rw [graph2Rename] at hs' ht' hn'
 have f1 := andRight hf
 have f2 := andRight f1
 have f3 := andRight f2
 have f4 := andRight f3
 apply translationCases R (certificate.relabel rho) (parameter.relabel rho) (numericCertificate.relabel rho)
   (v 0) (v 12) (v 1) (v 13) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) _
   (andLeft hf) (andLeft f1) (andLeft f2) (andLeft f3) (andLeft f4) hn'
 intro gamma eta Xi w heta hm hq hr htq htr htail hrest hpay hcert
 simp only [graph3Rename,sucRelabel,zRelabel]
 have hf' := renameInto hf eta Xi heta
 rw [factsRename] at hf'
 have hs'' := renameInto hs' eta Xi heta
 have ht'' := renameInto ht' eta Xi heta
 rw [graph2Rename] at hs'' ht''
 exact atTranslated R ((source.relabel rho).relabel eta) ((target.relabel rho).relabel eta)
   ((certificate.relabel rho).relabel eta) ((parameter.relabel rho).relabel eta)
   ((observedSource.relabel rho).relabel eta) ((observedTarget.relabel rho).relabel eta)
   ((numericCertificate.relabel rho).relabel eta) (fun i => (v i).relabel eta) w
   hf' hm hq hr htq htr htail hrest hpay hcert hs'' ht''
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeProof
