module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorConsCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalTypedArgumentObservations OriginalTypedArgumentObservationsAccumulatorSyntaxProof
open OriginalTypedArgumentObservationsAccumulatorQueryProof OriginalTypedArgumentObservationsInternalIterationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] walk walkStep

theorem consSuccessor (R : Program 2)
 (count raw acc1 acc2 suffix initial1 initial2 parameter out1 out2 remaining1 remaining2 result1 result2 typ child tail : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (accumulatorRow R count)))
 (hp1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial1 raw acc1)))
 (hp2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial2 raw acc2)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append acc2 acc1 suffix)))
 (hr1 : Nonempty (Derivation body Delta (graph3 (walk R) out1 (suc count) initial1 parameter)))
 (hr2 : Nonempty (Derivation body Delta (graph3 (walk R) out2 (suc count) initial2 parameter)))
 (hout1 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out1 remaining1 result1)))
 (hout2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out2 remaining2 result2)))
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail)))
 : Nonempty (Derivation body Delta (equal remaining1 remaining2 ⊓
   graph2 InternalApplicationValidityStackAppend.append result2 result1 suffix)) := by
 apply binaryCases InternalPairing.pairing typ child _
 intro beta1 j1 Theta1 packed hj1 hpacked
 simp only [conjunctionRename,equalRename,graph2Rename]
 have hrow_1 := renameInto hrow j1 Theta1 hj1
 simp only [accumulatorRename] at hrow_1
 have hp1_1 := renameInto hp1 j1 Theta1 hj1
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp1_1
 have hp2_1 := renameInto hp2 j1 Theta1 hj1
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp2_1
 have ha_1 := renameInto ha j1 Theta1 hj1
 simp only [graph2Rename,graph3Rename,sucRelabel] at ha_1
 have hr1_1 := renameInto hr1 j1 Theta1 hj1
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr1_1
 have hr2_1 := renameInto hr2 j1 Theta1 hj1
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr2_1
 have hout1_1 := renameInto hout1 j1 Theta1 hj1
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout1_1
 have hout2_1 := renameInto hout2 j1 Theta1 hj1
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout2_1
 have hc_1 := renameInto hc j1 Theta1 hj1
 simp only [graph2Rename,graph3Rename,sucRelabel] at hc_1
 apply binaryCases R packed (parameter.relabel j1) _
 intro beta2 j2 Theta2 observed hj2 hobserved
 simp only [conjunctionRename,equalRename,graph2Rename]
 have hrow_2 := renameInto hrow_1 j2 Theta2 hj2
 simp only [accumulatorRename] at hrow_2
 have hp1_2 := renameInto hp1_1 j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp1_2
 have hp2_2 := renameInto hp2_1 j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp2_2
 have ha_2 := renameInto ha_1 j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,sucRelabel] at ha_2
 have hr1_2 := renameInto hr1_1 j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr1_2
 have hr2_2 := renameInto hr2_1 j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr2_2
 have hout1_2 := renameInto hout1_1 j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout1_2
 have hout2_2 := renameInto hout2_1 j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout2_2
 have hc_2 := renameInto hc_1 j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,sucRelabel] at hc_2
 have hpacked_2 := renameInto hpacked j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,sucRelabel] at hpacked_2
 apply binaryCases InternalPairing.pairing ((typ.relabel j1).relabel j2) observed _
 intro beta3 j3 Theta3 typedObserved hj3 htypedObserved
 simp only [conjunctionRename,equalRename,graph2Rename]
 have hrow_3 := renameInto hrow_2 j3 Theta3 hj3
 simp only [accumulatorRename] at hrow_3
 have hp1_3 := renameInto hp1_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp1_3
 have hp2_3 := renameInto hp2_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp2_3
 have ha_3 := renameInto ha_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,sucRelabel] at ha_3
 have hr1_3 := renameInto hr1_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr1_3
 have hr2_3 := renameInto hr2_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr2_3
 have hout1_3 := renameInto hout1_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout1_3
 have hout2_3 := renameInto hout2_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout2_3
 have hc_3 := renameInto hc_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,sucRelabel] at hc_3
 have hpacked_3 := renameInto hpacked_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,sucRelabel] at hpacked_3
 have hobserved_3 := renameInto hobserved j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,sucRelabel] at hobserved_3
 apply binaryCases InternalListCodec.consCode typedObserved (((acc1.relabel j1).relabel j2).relabel j3) _
 intro beta4 j4 Theta4 nextAcc1 hj4 hnextAcc1
 simp only [conjunctionRename,equalRename,graph2Rename]
 have hrow_4 := renameInto hrow_3 j4 Theta4 hj4
 simp only [accumulatorRename] at hrow_4
 have hp1_4 := renameInto hp1_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp1_4
 have hp2_4 := renameInto hp2_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp2_4
 have ha_4 := renameInto ha_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,sucRelabel] at ha_4
 have hr1_4 := renameInto hr1_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr1_4
 have hr2_4 := renameInto hr2_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr2_4
 have hout1_4 := renameInto hout1_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout1_4
 have hout2_4 := renameInto hout2_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout2_4
 have hc_4 := renameInto hc_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,sucRelabel] at hc_4
 have hpacked_4 := renameInto hpacked_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,sucRelabel] at hpacked_4
 have hobserved_4 := renameInto hobserved_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,sucRelabel] at hobserved_4
 have htypedObserved_4 := renameInto htypedObserved j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,sucRelabel] at htypedObserved_4
 apply binaryCases InternalListCodec.consCode (typedObserved.relabel j4) ((((acc2.relabel j1).relabel j2).relabel j3).relabel j4) _
 intro beta5 j5 Theta5 nextAcc2 hj5 hnextAcc2
 simp only [conjunctionRename,equalRename,graph2Rename]
 have hrow_5 := renameInto hrow_4 j5 Theta5 hj5
 simp only [accumulatorRename] at hrow_5
 have hp1_5 := renameInto hp1_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp1_5
 have hp2_5 := renameInto hp2_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp2_5
 have ha_5 := renameInto ha_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,sucRelabel] at ha_5
 have hr1_5 := renameInto hr1_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr1_5
 have hr2_5 := renameInto hr2_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr2_5
 have hout1_5 := renameInto hout1_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout1_5
 have hout2_5 := renameInto hout2_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout2_5
 have hc_5 := renameInto hc_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,sucRelabel] at hc_5
 have hpacked_5 := renameInto hpacked_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,sucRelabel] at hpacked_5
 have hobserved_5 := renameInto hobserved_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,sucRelabel] at hobserved_5
 have htypedObserved_5 := renameInto htypedObserved_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,sucRelabel] at htypedObserved_5
 have hnextAcc1_5 := renameInto hnextAcc1 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,sucRelabel] at hnextAcc1_5
 apply binaryCases InternalPairing.pairing (((((tail.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5) (nextAcc1.relabel j5) _
 intro beta6 j6 Theta6 nextState1 hj6 hnextState1
 simp only [conjunctionRename,equalRename,graph2Rename]
 have hrow_6 := renameInto hrow_5 j6 Theta6 hj6
 simp only [accumulatorRename] at hrow_6
 have hp1_6 := renameInto hp1_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp1_6
 have hp2_6 := renameInto hp2_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp2_6
 have ha_6 := renameInto ha_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at ha_6
 have hr1_6 := renameInto hr1_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr1_6
 have hr2_6 := renameInto hr2_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr2_6
 have hout1_6 := renameInto hout1_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout1_6
 have hout2_6 := renameInto hout2_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout2_6
 have hc_6 := renameInto hc_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at hc_6
 have hpacked_6 := renameInto hpacked_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at hpacked_6
 have hobserved_6 := renameInto hobserved_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at hobserved_6
 have htypedObserved_6 := renameInto htypedObserved_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at htypedObserved_6
 have hnextAcc1_6 := renameInto hnextAcc1_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at hnextAcc1_6
 have hnextAcc2_6 := renameInto hnextAcc2 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,sucRelabel] at hnextAcc2_6
 apply binaryCases InternalPairing.pairing ((((((tail.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6) (nextAcc2.relabel j6) _
 intro beta7 j7 Theta7 nextState2 hj7 hnextState2
 simp only [conjunctionRename,equalRename,graph2Rename]
 have hrow_7 := renameInto hrow_6 j7 Theta7 hj7
 simp only [accumulatorRename] at hrow_7
 have hp1_7 := renameInto hp1_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp1_7
 have hp2_7 := renameInto hp2_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at hp2_7
 have ha_7 := renameInto ha_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at ha_7
 have hr1_7 := renameInto hr1_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr1_7
 have hr2_7 := renameInto hr2_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at hr2_7
 have hout1_7 := renameInto hout1_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout1_7
 have hout2_7 := renameInto hout2_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at hout2_7
 have hc_7 := renameInto hc_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at hc_7
 have hpacked_7 := renameInto hpacked_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at hpacked_7
 have hobserved_7 := renameInto hobserved_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at hobserved_7
 have htypedObserved_7 := renameInto htypedObserved_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at htypedObserved_7
 have hnextAcc1_7 := renameInto hnextAcc1_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at hnextAcc1_7
 have hnextAcc2_7 := renameInto hnextAcc2_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at hnextAcc2_7
 have hnextState1_7 := renameInto hnextState1 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,sucRelabel] at hnextState1_7
 have steps := OriginalTypedArgumentObservationsAccumulatorConsProof.consSuffix R
   (((((((initial1.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((initial2.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((raw.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((acc1.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((acc2.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((suffix.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((parameter.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((typ.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((child.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((tail.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) ((((((packed.relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((observed.relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) ((((typedObserved.relabel j4).relabel j5).relabel j6).relabel j7) (((nextAcc1.relabel j5).relabel j6).relabel j7) ((nextAcc2.relabel j6).relabel j7) (nextState1.relabel j7) nextState2
   hp1_7 hp2_7 ha_7 hc_7 hpacked_7 hobserved_7 htypedObserved_7 hnextAcc1_7 hnextAcc2_7 hnextState1_7 hnextState2
 obtain ⟨steps⟩ := steps
 have hstep1 := Nonempty.intro (Derivation.conjunctionLeft steps)
 have hstep2 := Nonempty.intro (Derivation.conjunctionLeft (Derivation.conjunctionRight steps))
 have happ := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionRight steps))
 have hrun1 := walkAfterFirstRecover R (((((((count.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((initial1.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (nextState1.relabel j7) (((((((out1.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((parameter.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) hstep1 hr1_7
 have hrun2 := walkAfterFirstRecover R (((((((count.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((initial2.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) nextState2 (((((((out2.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((parameter.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) hstep2 hr2_7
 exact accumulatorApply R (((((((count.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((tail.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((nextAcc1.relabel j5).relabel j6).relabel j7) ((nextAcc2.relabel j6).relabel j7) (((((((suffix.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (nextState1.relabel j7) nextState2 (((((((parameter.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((out1.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((out2.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((remaining1.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((remaining2.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((result1.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (((((((result2.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7)
   hrow_7 hnextState1_7 hnextState2 happ hrun1 hrun2 hout1_7 hout2_7

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorConsCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorConsCoreProof
