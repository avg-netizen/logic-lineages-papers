module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorSuccessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalAbsorbProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalTypedArgumentObservations
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalLessThanSupportProof (oneConstantValue)
open InternalRawListRecursionSupportProof (recursionNext)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalTypedArgumentObservationsAccumulatorSyntaxProof

open OriginalTypedArgumentObservationsAccumulatorSuccessorProof

attribute [local irreducible] walk walkStep

theorem zeroRow (R : Program 2) : Nonempty (Derivation body Delta (accumulatorRow R z)) := by
 unfold accumulatorRow
 apply actualFiniteUniversalIntroduction body alpha 13 Delta
 let raw : OTerm (alpha ⊕ Fin 13) := .var (.inr 0)
 let acc1 : OTerm (alpha ⊕ Fin 13) := .var (.inr 1)
 let acc2 : OTerm (alpha ⊕ Fin 13) := .var (.inr 2)
 let suffix : OTerm (alpha ⊕ Fin 13) := .var (.inr 3)
 let initial1 : OTerm (alpha ⊕ Fin 13) := .var (.inr 4)
 let initial2 : OTerm (alpha ⊕ Fin 13) := .var (.inr 5)
 let parameter : OTerm (alpha ⊕ Fin 13) := .var (.inr 6)
 let out1 : OTerm (alpha ⊕ Fin 13) := .var (.inr 7)
 let out2 : OTerm (alpha ⊕ Fin 13) := .var (.inr 8)
 let remaining1 : OTerm (alpha ⊕ Fin 13) := .var (.inr 9)
 let remaining2 : OTerm (alpha ⊕ Fin 13) := .var (.inr 10)
 let result1 : OTerm (alpha ⊕ Fin 13) := .var (.inr 11)
 let result2 : OTerm (alpha ⊕ Fin 13) := .var (.inr 12)
 let c : OTerm (alpha ⊕ Fin 13) := z
 let H0 := graph2 InternalPairing.pairing initial1 raw acc1
 let H1 := graph2 InternalPairing.pairing initial2 raw acc2
 let H2 := graph2 InternalApplicationValidityStackAppend.append acc2 acc1 suffix
 let H3 := graph3 (walk R) out1 c initial1 parameter
 let H4 := graph3 (walk R) out2 c initial2 parameter
 let H5 := graph2 InternalPairing.pairing out1 remaining1 result1
 let H6 := graph2 InternalPairing.pairing out2 remaining2 result2
 let Theta := H6 :: H5 :: H4 :: H3 :: H2 :: H1 :: H0 :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 13))
 have h0 : Nonempty (Derivation body Theta H0) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))⟩
 have h1 : Nonempty (Derivation body Theta H1) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))⟩
 have h2 : Nonempty (Derivation body Theta H2) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))⟩
 have h3 : Nonempty (Derivation body Theta H3) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
 have h4 : Nonempty (Derivation body Theta H4) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
 have h5 : Nonempty (Derivation body Theta H5) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
 have h6 : Nonempty (Derivation body Theta H6) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hfixed1 : Nonempty (Derivation body Theta (graph3 (walk R) initial1 c initial1 parameter)) := by
   simpa only [walk,c,OriginalUniverseDecoderInternalFuelNumericSyntaxProof.repeatGraph,OriginalUniverseDecoderInternalFuelNumericSyntaxProof.repeatProgram,OriginalUniverseDecoderInternalFuelNumericSyntaxProof.repeatStep] using OriginalUniverseDecoderInternalFuelNumericSupportProof.repeatZeroValue (walkStep R) initial1 parameter
 have hfixed2 : Nonempty (Derivation body Theta (graph3 (walk R) initial2 c initial2 parameter)) := by
   simpa only [walk,c,OriginalUniverseDecoderInternalFuelNumericSyntaxProof.repeatGraph,OriginalUniverseDecoderInternalFuelNumericSyntaxProof.repeatProgram,OriginalUniverseDecoderInternalFuelNumericSyntaxProof.repeatStep] using OriginalUniverseDecoderInternalFuelNumericSupportProof.repeatZeroValue (walkStep R) initial2 parameter
 obtain ⟨h⟩ := OriginalTypedArgumentObservationsAccumulatorFixedProof.fixedSuffix R c raw acc1 acc2 suffix initial1 initial2 parameter out1 out2 remaining1 remaining2 result1 result2
   h0 h1 h2 hfixed1 hfixed2 h3 h4 h5 h6
 simpa only [accumulatorBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))))))))

theorem successorRow (R : Program 2) (count : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (accumulatorRow R count))) :
 Nonempty (Derivation body Delta (accumulatorRow R (suc count))) := by
 unfold accumulatorRow
 apply actualFiniteUniversalIntroduction body alpha 13 Delta
 let raw : OTerm (alpha ⊕ Fin 13) := .var (.inr 0)
 let acc1 : OTerm (alpha ⊕ Fin 13) := .var (.inr 1)
 let acc2 : OTerm (alpha ⊕ Fin 13) := .var (.inr 2)
 let suffix : OTerm (alpha ⊕ Fin 13) := .var (.inr 3)
 let initial1 : OTerm (alpha ⊕ Fin 13) := .var (.inr 4)
 let initial2 : OTerm (alpha ⊕ Fin 13) := .var (.inr 5)
 let parameter : OTerm (alpha ⊕ Fin 13) := .var (.inr 6)
 let out1 : OTerm (alpha ⊕ Fin 13) := .var (.inr 7)
 let out2 : OTerm (alpha ⊕ Fin 13) := .var (.inr 8)
 let remaining1 : OTerm (alpha ⊕ Fin 13) := .var (.inr 9)
 let remaining2 : OTerm (alpha ⊕ Fin 13) := .var (.inr 10)
 let result1 : OTerm (alpha ⊕ Fin 13) := .var (.inr 11)
 let result2 : OTerm (alpha ⊕ Fin 13) := .var (.inr 12)
 let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 13)
 let H0 := graph2 InternalPairing.pairing initial1 raw acc1
 let H1 := graph2 InternalPairing.pairing initial2 raw acc2
 let H2 := graph2 InternalApplicationValidityStackAppend.append acc2 acc1 suffix
 let H3 := graph3 (walk R) out1 (suc c) initial1 parameter
 let H4 := graph3 (walk R) out2 (suc c) initial2 parameter
 let H5 := graph2 InternalPairing.pairing out1 remaining1 result1
 let H6 := graph2 InternalPairing.pairing out2 remaining2 result2
 let Theta := H6 :: H5 :: H4 :: H3 :: H2 :: H1 :: H0 :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 13))
 have ih := renameInto hrow Sum.inl Theta (fun p hp => (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)))))))))
 rw [accumulatorRename] at ih
 have h0 : Nonempty (Derivation body Theta H0) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))⟩
 have h1 : Nonempty (Derivation body Theta H1) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))⟩
 have h2 : Nonempty (Derivation body Theta H2) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))⟩
 have h3 : Nonempty (Derivation body Theta H3) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
 have h4 : Nonempty (Derivation body Theta H4) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
 have h5 : Nonempty (Derivation body Theta H5) := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
 have h6 : Nonempty (Derivation body Theta H6) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := successorCore R c raw acc1 acc2 suffix initial1 initial2 parameter out1 out2 remaining1 remaining2 result1 result2 ih h0 h1 h2 h3 h4 h5 h6
 simpa only [accumulatorBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))))))))

theorem allRows (R : Program 2) (count : OTerm alpha) :
 Nonempty (Derivation body Delta (accumulatorRow R count)) := by
 let theta : Formula (alpha ⊕ Fin 1) := accumulatorRow R (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,accumulatorInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta) R)
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := successorRow (body := body) (Delta := theta :: Delta.map weaken)
     R (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,accumulatorSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
 simpa only [theta,accumulatorInstantiate,varBind] using (Nonempty.intro h)

theorem accumulatorSuffix : OriginalTypedArgumentObservationsAccumulatorTargets.AccumulatorSuffix := by
 intro R body alpha Delta count raw acc1 acc2 suffix initial1 initial2 parameter out1 out2 remaining1 remaining2 result1 result2 h0 h1 h2 h3 h4 h5 h6
 exact accumulatorApply R count raw acc1 acc2 suffix initial1 initial2 parameter out1 out2 remaining1 remaining2 result1 result2 (allRows R count) h0 h1 h2 h3 h4 h5 h6

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorProof
