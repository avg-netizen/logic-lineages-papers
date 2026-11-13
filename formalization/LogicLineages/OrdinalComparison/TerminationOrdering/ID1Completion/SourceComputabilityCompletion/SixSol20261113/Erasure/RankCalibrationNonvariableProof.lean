module
public import Mathlib.Tactic.FinCases
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNonvariableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel)
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open RankMemoDefinitions RankCalibrationInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
/-- Honest zero exclusion plus actual successor branch, for each nonvariable
source tag. Arbitrary actual E-code is retained; the IH is transported only by
its proved code equality. -/
theorem actualNonvariable (R : Program 2) (H G : Program 1) (M W : Program 2)
 (index : Fin 5) (code input parameter rank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta (RankCalibrationInductionDefinitions.BelowRaw R H G M W code)))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) code input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (index.val+1)) input))) :
 Nonempty (Derivation body Delta (graph1 decoder rank code)) := by
 apply zeroSuccessorCases Delta code _
 · have hn := RankCalibrationBaseProof.actualNonvariableNonzero R H G M W body alpha Delta input parameter code index hs hv ht
   simp only [equalEqn] at hn
   obtain ⟨hn⟩ := withHyp hn (eqn code z)
   exact ⟨Derivation.explosion (Derivation.implicationElimination hn (Derivation.hypothesis List.mem_cons_self))⟩
 · intro beta j Theta stage hj he
   rw [graph1Rename]
   have ih' := renameInto ih j Theta hj
   have hs' := renameInto hs j Theta hj
   have hv' := renameInto hv j Theta hj
   have hr' := renameInto hr j Theta hj
   have ht' := renameInto ht j Theta hj
   simp only [graph1Rename,graph2Rename,belowRawRename,GuardedSourceSyntaxProof.numeralRename] at ih' hs' hv' hr' ht'
   have ihs := RankCalibrationInductionTransportProof.belowTransport R H G M W (code.relabel j) (suc stage) he ih'
   have hvs := outputTransport (OriginalHereditaryEvaluatorDefinitions.evaluator R) (code.relabel j) (suc stage)
     (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hv'
   have hd : Nonempty (Derivation body Theta (graph1 decoder (rank.relabel j) (suc stage))) := by
     fin_cases index
     · exact RankCalibrationLambdaProof.actualLambda R H G M W stage (input.relabel j) (parameter.relabel j) (rank.relabel j) ihs hs' hvs hr' ht'
     · exact RankCalibrationApplicationProof.actualApplication R H G M W stage (input.relabel j) (parameter.relabel j) (rank.relabel j) ihs hs' hvs hr' ht'
     · exact RankCalibrationBaseProof.actualBottom R H G M W body beta Theta (input.relabel j) (parameter.relabel j) (suc stage) (rank.relabel j) hs' hvs hr' ht'
     · exact RankCalibrationOrdinaryProof.actualOrdinary R H G M W stage (input.relabel j) (parameter.relabel j) (rank.relabel j) ihs hs' hvs hr' ht'
     · exact RankCalibrationNumberedProof.actualNumbered R H G M W stage (input.relabel j) (parameter.relabel j) (rank.relabel j) ihs hs' hvs hr' ht'
   obtain ⟨he⟩ := he
   exact headTransport decoder (rank.relabel j) (suc stage) (code.relabel j) Fin.elim0
     ⟨InternalTagArithmeticSupportProof.symm he⟩ hd
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNonvariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNonvariableProof
