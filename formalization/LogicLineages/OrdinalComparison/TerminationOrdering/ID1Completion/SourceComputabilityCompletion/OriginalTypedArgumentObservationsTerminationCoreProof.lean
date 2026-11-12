module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open OriginalTypedArgumentObservations OriginalTypedArgumentObservationsTerminationSyntaxProof
open OriginalTypedArgumentObservationsInternalStepProof OriginalTypedArgumentObservationsInternalIterationProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro)
open OriginalUniverseDecoderInternalFuelNumericFixedProof (fixedValue)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] walk walkStep advance

theorem twoRename {beta : Type} (a b : OTerm alpha) (j : alpha → beta) :
 (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm alpha) i).relabel j) = ![a.relabel j,b.relabel j] := by
 funext i
 exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

theorem fixedFromRun (R : Program 2) (count initial parameter out : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (graph2 (walkStep R) initial initial parameter)))
 (hr : Nonempty (Derivation body Delta (graph3 (walk R) out count initial parameter))) :
 Nonempty (Derivation body Delta (graph2 (walkStep R) out out parameter)) := by
 have hz : Nonempty (Derivation body Delta (graph3 (walk R) initial count initial parameter)) := by
   simpa only [walk,OriginalUniverseDecoderInternalFuelNumericSyntaxProof.repeatGraph,
     OriginalUniverseDecoderInternalFuelNumericSyntaxProof.repeatProgram,OriginalUniverseDecoderInternalFuelNumericSyntaxProof.repeatStep] using fixedValue (walkStep R) count initial parameter hf
 obtain ⟨he⟩ := valueUnique (walk R) initial out ![count,initial,parameter] hz hr
 have ho := outputTransport (walkStep R) initial out ![initial,parameter] ⟨he⟩ hf
 exact headTransport (walkStep R) out initial out ![parameter] ⟨he⟩ ho

theorem consTerminal (R : Program 2) (count raw acc initial parameter out typ child tail : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (terminalRow R count)))
 (hb : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw (suc count))))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial raw acc)))
 (hr : Nonempty (Derivation body Delta (graph3 (walk R) out (suc count) initial parameter)))
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail))) :
 Nonempty (Derivation body Delta (graph2 (walkStep R) out out parameter)) := by
 let xs : Fin 2 → OTerm alpha := ![initial,parameter]
 let listP := consOf (typedObservation R) accumulated
 apply programCases listP xs _
 intro beta j Theta nextAcc hj ha
 simp only [xs,twoRename] at ha
 rw [graph2Rename]
 have hp' := renameInto hp j Theta hj
 have hc' := renameInto hc j Theta hj
 have hb' := renameInto hb j Theta hj
 have hr' := renameInto hr j Theta hj
 have hrow' := renameInto hrow j Theta hj
 simp only [graph2Rename] at hp'
 simp only [graph3Rename] at hc' hr'
 simp only [sucRelabel] at hr'
 simp only [InternalLessThan.strictLess,orderRename,sucRelabel] at hb'
 rw [terminalRename] at hrow'
 let ys : Fin 2 → OTerm beta := ![initial.relabel j,parameter.relabel j]
 have hrem := stateRemaining (initial.relabel j) (raw.relabel j) (acc.relabel j) (parameter.relabel j) hp'
 have htail := consTail remaining (raw.relabel j) (typ.relabel j) (child.relabel j) (tail.relabel j) ys hrem hc'
 apply programCases (advance R) ys _
 intro gamma k Xi next hk hn
 simp only [ys,twoRename] at hn
 rw [graph2Rename]
 have hp'' := renameInto hp' k Xi hk
 have hc'' := renameInto hc' k Xi hk
 have hb'' := renameInto hb' k Xi hk
 have hr'' := renameInto hr' k Xi hk
 have hrow'' := renameInto hrow' k Xi hk
 have htail' := renameInto htail k Xi hk
 have ha' := renameInto ha k Xi hk
 simp only [graph2Rename] at hp''
 simp only [graph3Rename,sucRelabel] at hc'' hr''
 simp only [InternalLessThan.strictLess,orderRename,sucRelabel] at hb''
 rw [terminalRename] at hrow''
 simp only [programRename,ys,twoRename] at htail' ha'
 let zs : Fin 2 → OTerm gamma := ![(initial.relabel j).relabel k,(parameter.relabel j).relabel k]
 have hpair : Nonempty (Derivation body Xi (graph2 InternalPairing.pairing next ((tail.relabel j).relabel k) (nextAcc.relabel k))) := by
   apply binaryRecover InternalPairing.pairing tailRaw listP next ((tail.relabel j).relabel k) (nextAcc.relabel k) zs
   · simpa only [advance,pairOf,listP,zs] using hn
   · exact htail'
   · exact ha'
 have hrem' := stateRemaining ((initial.relabel j).relabel k) ((raw.relabel j).relabel k)
   ((acc.relabel j).relabel k) ((parameter.relabel j).relabel k) hp''
 have hstep : Nonempty (Derivation body Xi (graph2 (walkStep R) next ((initial.relabel j).relabel k) ((parameter.relabel j).relabel k))) := by
   unfold walkStep
   exact sameYesIntro (leftOf remaining) (OriginalRawSyntaxTransport.constant 2 7) (advance R) (.projection 0)
     next (numeral 7) (numeral 7) zs
     (consTag remaining ((raw.relabel j).relabel k) ((typ.relabel j).relabel k) ((child.relabel j).relabel k)
       ((tail.relabel j).relabel k) zs hrem' hc'') (constantValue 7 zs)
     (by simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body := body) (Gamma := Xi) (numeral 7)))) hn
 have ht := OriginalTypedArgumentObservationsInternalBoundProof.rawTailBound
   ((raw.relabel j).relabel k) ((typ.relabel j).relabel k) ((child.relabel j).relabel k)
   ((tail.relabel j).relabel k) hc''
 have hsmall := InternalSquareRootArithmeticSupportProof.strictWeakTrans
   ((tail.relabel j).relabel k) ((raw.relabel j).relabel k) ((count.relabel j).relabel k) ht hb''
 have hrun := walkAfterFirstRecover R ((count.relabel j).relabel k) ((initial.relabel j).relabel k)
   next ((out.relabel j).relabel k) ((parameter.relabel j).relabel k) hstep hr''
 exact terminalApply R ((count.relabel j).relabel k) ((tail.relabel j).relabel k) (nextAcc.relabel k)
   next ((parameter.relabel j).relabel k) ((out.relabel j).relabel k) hrow'' hsmall hpair hrun

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationCoreProof
