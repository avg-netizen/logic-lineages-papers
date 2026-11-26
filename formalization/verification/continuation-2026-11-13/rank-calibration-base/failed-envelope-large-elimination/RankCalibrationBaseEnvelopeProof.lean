module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationEnvelopeQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseEnvelopeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (suc z eqn)
open InternalTagArithmeticSupportProof (refl symm)
open InternalPairingSumBounds (weakBound)
open InternalOriginalPairingOrderArithmeticProof (weakTransport strictWeakConflict withHyp)
open InternalUnpairReverseBoundsArithmeticProof (weakTrans)

theorem nonzeroFromBound (k : Nat) (code : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (weakBound (suc (numeral k)) code))) :
 Nonempty (Derivation body Delta ((equal code z).not)) := by
 rw [equalEqn]
 apply Nonempty.intro
 apply Derivation.implicationIntroduction
 have hz : Nonempty (Derivation body (eqn code z :: Delta) (eqn code z)) :=
   ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨hz⟩ := hz
 have hbound := weakTransport (suc (numeral k)) z (suc (numeral k)) code
   ⟨refl _⟩ ⟨symm hz⟩ (withHyp hb (eqn code z))
 exact Classical.choice (strictWeakConflict z (suc (numeral k)) (⊥ : Formula alpha)
   ⟨InternalQuotientComparisonProof.zeroLessSuccessor (numeral k)⟩ hbound)

theorem atEnvelope (R : Program 2) (H G : Program 1) (M W : Program 2)
 (k : Fin 5) (input parameter typ raw code base inner root rows observed : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) code input parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (k.val+1)) input)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing code base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left observed root))) :
 Nonempty (Derivation body Delta ((equal code (numeral 0)).not)) := by
 have he := RankCalibrationBaseTagProof.observedTag R H G M W ⟨k.val+1,Nat.succ_lt_succ k.isLt⟩
   input parameter typ raw code base inner root rows observed hs hv hp ht ho hi hl
 rw [equalEqn] at he
 obtain ⟨he⟩ := he
 have hb := weakTrans observed root code (ObservationDescentPairProof.leftBound root observed hl)
   (ObservationDescentPairProof.envelope code base inner root rows ho hi)
 have hb' := weakTransport (numeral (k.val+1)) code observed code ⟨symm he⟩ ⟨refl code⟩ hb
 exact nonzeroFromBound k.val code hb'

theorem memoTag (R : Program 2) (H G : Program 1) (M W : Program 2)
 (k : Fin 6) (stage tab input parameter typ raw base inner root rows : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) (suc stage) input parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral k.val) input)))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (suc stage) base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows))) :
 Nonempty (Derivation body Delta (graph2 RankMemoDefinitions.tag (numeral k.val) stage tab)) := by
 apply InternalAcceptanceSupportProof.programCases InternalUnpair.left (Fin.cons root Fin.elim0) _
 intro beta j Theta observed hj hl
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hp' := renameInto hp j Theta hj
 have ht' := renameInto ht j Theta hj
 have ho' := renameInto ho j Theta hj
 have hi' := renameInto hi j Theta hj
 simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,InternalTagArithmeticSyntaxProof.sucRelabel] at hs' hv' hp' ht' ho' hi'
 simp only [consTermRename,emptyRename] at hl
 have he := RankCalibrationBaseTagProof.observedTag R H G M W k
   (input.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (suc (stage.relabel j))
   (base.relabel j) (inner.relabel j) (root.relabel j) (rows.relabel j) observed hs' hv' hp' ht' ho' hi' hl
 rw [equalEqn] at he
 have hl' := outputTransport InternalUnpair.left observed (numeral k.val) (Fin.cons (root.relabel j) Fin.elim0) he hl
 exact unaryValue InternalUnpair.left RankMemoDefinitions.recursiveRoot (numeral k.val) (root.relabel j)
   (![stage.relabel j,tab.relabel j]) hl'
   (RankMemoOpeningProof.rootValue (stage.relabel j) (tab.relabel j) (suc (stage.relabel j))
     (base.relabel j) (inner.relabel j) (root.relabel j) (rows.relabel j) ⟨refl _⟩ ho' hi')
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseEnvelopeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseEnvelopeProof
