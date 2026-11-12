module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelLowerBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomTwoTickProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimePaddingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomFuelProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (trans symm cancelSuc addSucc)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalOriginalOrderProof (orderCases)
open InternalSliceInductionSyntaxProof (eqnRename)
open InternalNumericIterationFixedPointProof InternalNumericIterationFusionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem padTwo (R : Program 2) (input output fuel : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output (suc (suc z)) input)))
 (he : Nonempty (Derivation body Delta (graph1 InternalUnpair.left z output)))
 (hb : Nonempty (Derivation body Delta (ltF (suc (suc z)) (suc fuel)))) :
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output fuel input)) := by
 apply orderCases Delta (suc (suc z)) (suc fuel) _ hb
 intro beta j Theta gap hj hgap
 simp only [graph2Rename]
 have hr' := renameInto hr j Theta hj
 have he' := renameInto he j Theta hj
 simp only [graph2Rename,graph1Rename,zRelabel,sucRelabel] at hr' he'
 simp only [zRelabel,sucRelabel] at hgap
 have hfixed := fixedValue (OriginalHereditaryCombinedStep.step R) gap (output.relabel j)
   (OriginalHereditaryPotentialCompletionEmptyProof.fixedEmpty R (output.relabel j) he')
 have hlong := fusionValue (OriginalHereditaryCombinedStep.step R) (suc (suc z)) gap (input.relabel j) (output.relabel j) (output.relabel j) hr' hfixed
 have hcount := cancelSuc (trans (symm (addSucc (suc (suc z)) gap)) (Classical.choice hgap))
 exact headTransport (OriginalHereditaryRuntimeIterationDefinitions.run R) (output.relabel j)
   (add (suc (suc z)) gap) (fuel.relabel j) (Fin.cons (input.relabel j) Fin.elim0) ⟨hcount⟩ hlong

theorem actualFuel : OriginalInternalBottomFuelTargets.ActualFuel := by
 intro R body alpha Delta raw typ packed c parameter rawJob typed job visitFrame work input counts payload frame returnWork middle root tail value stack output fuel
   hb hpacked hp hr ht hj hv hs hc hpay hf hm htail hvalue hout hw hret hstack hroot hFuel
 have htwo := OriginalInternalBottomTwoTickProof.actualTwoTick R body alpha Delta raw typ packed c parameter rawJob typed job visitFrame work input counts payload frame returnWork middle root tail value stack output
   hb hpacked hp hr ht hj hv hs hc hpay hf hm htail hvalue hout hw hret hstack hroot
 exact padTwo R input output fuel htwo (pairLeft output z stack hout)
   (OriginalHereditaryFuelLowerBoundProof.actualLowerBound job fuel hFuel)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomFuelProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomFuelProof
