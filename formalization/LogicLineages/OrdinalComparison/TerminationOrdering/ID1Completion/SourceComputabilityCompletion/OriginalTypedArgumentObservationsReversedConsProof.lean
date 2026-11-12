module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsConsRunsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReversedConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalTypedArgumentObservations
open OriginalTypedArgumentObservationsAccumulatorQueryProof OriginalTypedArgumentObservationsWalkQueryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] walk walked reversedObservations

theorem reversedConsCases (R : Program 2)
 (raw typ child tail packed observation typedObservation parameter : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ child tail)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ child)))
 (ho : Nonempty (Derivation body Delta (graph2 R observation packed parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typedObservation typ observation)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (singleton combined tailReversed : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode singleton (typedObservation.relabel j) z)) →
   Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append combined tailReversed singleton)) →
   Nonempty (Derivation body Theta (graph2 (reversedObservations R) combined (raw.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 (reversedObservations R) tailReversed (tail.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 apply binaryCases InternalListCodec.consCode typedObservation z _
 intro beta1 j1 Theta1 singleton hj1 hsingleton
 simp only [zRelabel,sucRelabel] at hsingleton
 have hc_1 := renameInto hc j1 Theta1 hj1
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hc_1
 have hp_1 := renameInto hp j1 Theta1 hj1
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hp_1
 have ho_1 := renameInto ho j1 Theta1 hj1
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ho_1
 have ht_1 := renameInto ht j1 Theta1 hj1
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ht_1
 apply binaryCases InternalPairing.pairing (raw.relabel j1) z _
 intro beta2 j2 Theta2 initialParent hj2 hinitialParent
 simp only [zRelabel,sucRelabel] at hinitialParent
 have hc_2 := renameInto hc_1 j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hc_2
 have hp_2 := renameInto hp_1 j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hp_2
 have ho_2 := renameInto ho_1 j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ho_2
 have ht_2 := renameInto ht_1 j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ht_2
 have hsingleton_2 := renameInto hsingleton j2 Theta2 hj2
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hsingleton_2
 apply binaryCases InternalPairing.pairing ((tail.relabel j1).relabel j2) z _
 intro beta3 j3 Theta3 initialTail hj3 hinitialTail
 simp only [zRelabel,sucRelabel] at hinitialTail
 have hc_3 := renameInto hc_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hc_3
 have hp_3 := renameInto hp_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hp_3
 have ho_3 := renameInto ho_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ho_3
 have ht_3 := renameInto ht_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ht_3
 have hsingleton_3 := renameInto hsingleton_2 j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hsingleton_3
 have hinitialParent_3 := renameInto hinitialParent j3 Theta3 hj3
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialParent_3
 apply binaryCases InternalPairing.pairing (((tail.relabel j1).relabel j2).relabel j3) ((singleton.relabel j2).relabel j3) _
 intro beta4 j4 Theta4 initialSingleton hj4 hinitialSingleton
 have hc_4 := renameInto hc_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hc_4
 have hp_4 := renameInto hp_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hp_4
 have ho_4 := renameInto ho_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ho_4
 have ht_4 := renameInto ht_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ht_4
 have hsingleton_4 := renameInto hsingleton_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hsingleton_4
 have hinitialParent_4 := renameInto hinitialParent_3 j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialParent_4
 have hinitialTail_4 := renameInto hinitialTail j4 Theta4 hj4
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialTail_4
 apply ternaryCases (walk R) (suc ((((raw.relabel j1).relabel j2).relabel j3).relabel j4)) ((initialParent.relabel j3).relabel j4) ((((parameter.relabel j1).relabel j2).relabel j3).relabel j4) _
 intro beta5 j5 Theta5 outParent hj5 houtParent
 simp only [zRelabel,sucRelabel] at houtParent
 have hc_5 := renameInto hc_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hc_5
 have hp_5 := renameInto hp_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hp_5
 have ho_5 := renameInto ho_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ho_5
 have ht_5 := renameInto ht_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ht_5
 have hsingleton_5 := renameInto hsingleton_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hsingleton_5
 have hinitialParent_5 := renameInto hinitialParent_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialParent_5
 have hinitialTail_5 := renameInto hinitialTail_4 j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialTail_5
 have hinitialSingleton_5 := renameInto hinitialSingleton j5 Theta5 hj5
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialSingleton_5
 apply ternaryCases (walk R) (suc (((((tail.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5)) ((initialTail.relabel j4).relabel j5) (((((parameter.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5) _
 intro beta6 j6 Theta6 outTailOwn hj6 houtTailOwn
 simp only [zRelabel,sucRelabel] at houtTailOwn
 have hc_6 := renameInto hc_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hc_6
 have hp_6 := renameInto hp_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hp_6
 have ho_6 := renameInto ho_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ho_6
 have ht_6 := renameInto ht_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ht_6
 have hsingleton_6 := renameInto hsingleton_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hsingleton_6
 have hinitialParent_6 := renameInto hinitialParent_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialParent_6
 have hinitialTail_6 := renameInto hinitialTail_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialTail_6
 have hinitialSingleton_6 := renameInto hinitialSingleton_5 j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialSingleton_6
 have houtParent_6 := renameInto houtParent j6 Theta6 hj6
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at houtParent_6
 apply ternaryCases (walk R) ((((((raw.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6) (((initialTail.relabel j4).relabel j5).relabel j6) ((((((parameter.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6) _
 intro beta7 j7 Theta7 outTailLong hj7 houtTailLong
 have hc_7 := renameInto hc_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hc_7
 have hp_7 := renameInto hp_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hp_7
 have ho_7 := renameInto ho_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ho_7
 have ht_7 := renameInto ht_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ht_7
 have hsingleton_7 := renameInto hsingleton_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hsingleton_7
 have hinitialParent_7 := renameInto hinitialParent_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialParent_7
 have hinitialTail_7 := renameInto hinitialTail_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialTail_7
 have hinitialSingleton_7 := renameInto hinitialSingleton_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialSingleton_7
 have houtParent_7 := renameInto houtParent_6 j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at houtParent_7
 have houtTailOwn_7 := renameInto houtTailOwn j7 Theta7 hj7
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at houtTailOwn_7
 apply pairCases ((outParent.relabel j6).relabel j7) _
 intro beta8 j8 Theta8 parentRemaining combined hj8 hparentRemaining
 have hc_8 := renameInto hc_7 j8 Theta8 hj8
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hc_8
 have hp_8 := renameInto hp_7 j8 Theta8 hj8
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hp_8
 have ho_8 := renameInto ho_7 j8 Theta8 hj8
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ho_8
 have ht_8 := renameInto ht_7 j8 Theta8 hj8
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ht_8
 have hsingleton_8 := renameInto hsingleton_7 j8 Theta8 hj8
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hsingleton_8
 have hinitialParent_8 := renameInto hinitialParent_7 j8 Theta8 hj8
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialParent_8
 have hinitialTail_8 := renameInto hinitialTail_7 j8 Theta8 hj8
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialTail_8
 have hinitialSingleton_8 := renameInto hinitialSingleton_7 j8 Theta8 hj8
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialSingleton_8
 have houtParent_8 := renameInto houtParent_7 j8 Theta8 hj8
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at houtParent_8
 have houtTailOwn_8 := renameInto houtTailOwn_7 j8 Theta8 hj8
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at houtTailOwn_8
 have houtTailLong_8 := renameInto houtTailLong j8 Theta8 hj8
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at houtTailLong_8
 apply pairCases ((outTailOwn.relabel j7).relabel j8) _
 intro beta9 j9 Theta9 tailRemaining tailReversed hj9 htailRemaining
 have hc_9 := renameInto hc_8 j9 Theta9 hj9
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hc_9
 have hp_9 := renameInto hp_8 j9 Theta9 hj9
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hp_9
 have ho_9 := renameInto ho_8 j9 Theta9 hj9
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ho_9
 have ht_9 := renameInto ht_8 j9 Theta9 hj9
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at ht_9
 have hsingleton_9 := renameInto hsingleton_8 j9 Theta9 hj9
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hsingleton_9
 have hinitialParent_9 := renameInto hinitialParent_8 j9 Theta9 hj9
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialParent_9
 have hinitialTail_9 := renameInto hinitialTail_8 j9 Theta9 hj9
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialTail_9
 have hinitialSingleton_9 := renameInto hinitialSingleton_8 j9 Theta9 hj9
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hinitialSingleton_9
 have houtParent_9 := renameInto houtParent_8 j9 Theta9 hj9
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at houtParent_9
 have houtTailOwn_9 := renameInto houtTailOwn_8 j9 Theta9 hj9
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at houtTailOwn_9
 have houtTailLong_9 := renameInto houtTailLong_8 j9 Theta9 hj9
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at houtTailLong_9
 have hparentRemaining_9 := renameInto hparentRemaining j9 Theta9 hj9
 simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hparentRemaining_9
 have result := OriginalTypedArgumentObservationsConsRunsProof.fromRuns R
   (((((((((raw.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) (((((((((typ.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) (((((((((child.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) (((((((((tail.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) (((((((((parameter.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) (((((((((packed.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) (((((((((observation.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) (((((((((typedObservation.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) ((((((((singleton.relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) (((((((initialParent.relabel j3).relabel j4).relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) ((((((initialTail.relabel j4).relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) (((((initialSingleton.relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) ((((outParent.relabel j6).relabel j7).relabel j8).relabel j9) (((outTailOwn.relabel j7).relabel j8).relabel j9) ((outTailLong.relabel j8).relabel j9) (parentRemaining.relabel j9) tailRemaining (combined.relabel j9) tailReversed
   hc_9 hp_9 ho_9 ht_9 hsingleton_9 hinitialParent_9 hinitialTail_9 hinitialSingleton_9 houtParent_9 houtTailOwn_9 houtTailLong_9 hparentRemaining_9 htailRemaining
 obtain ⟨result⟩ := result
 have hjall : ∀ f ∈ Delta, f.relabel (j9 ∘ (j8 ∘ (j7 ∘ (j6 ∘ (j5 ∘ (j4 ∘ (j3 ∘ (j2 ∘ j1)))))))) ∈ Theta9 := by
   intro f hf
   simpa only [formulaRelabelComposition] using (hj9 ((((((((f.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7).relabel j8) (hj8 (((((((f.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7) (hj7 ((((((f.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5).relabel j6) (hj6 (((((f.relabel j1).relabel j2).relabel j3).relabel j4).relabel j5) (hj5 ((((f.relabel j1).relabel j2).relabel j3).relabel j4) (hj4 (((f.relabel j1).relabel j2).relabel j3) (hj3 ((f.relabel j1).relabel j2) (hj2 (f.relabel j1) (hj1 f hf)))))))))
 have hnext := next beta9 (j9 ∘ (j8 ∘ (j7 ∘ (j6 ∘ (j5 ∘ (j4 ∘ (j3 ∘ (j2 ∘ j1)))))))) Theta9 ((((((((singleton.relabel j2).relabel j3).relabel j4).relabel j5).relabel j6).relabel j7).relabel j8).relabel j9) (combined.relabel j9) tailReversed hjall
   (by simpa only [Term.relabel_relabel] using hsingleton_9)
   ⟨Derivation.conjunctionLeft result⟩
   (by simpa only [Term.relabel_relabel] using (Nonempty.intro (Derivation.conjunctionLeft (Derivation.conjunctionRight result))))
   (by simpa only [Term.relabel_relabel] using (Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionRight result))))
 simpa only [formulaRelabelComposition] using hnext

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReversedConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReversedConsProof
