module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseSuccessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseNonzeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseProof
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
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalOriginalPairingOrderArithmeticProof (withHyp)

theorem actualVariable : RankCalibrationBaseTargets.ActualVariable := by
 intro R H G M W body alpha Delta input parameter code rank hs hv hr ht
 apply RankCalibrationBaseFieldsProof.leafCases 0 input _ ht
 intro beta j Theta typ raw field hj hp hc
 rw [graph1Rename]
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hr' := renameInto hr j Theta hj
 have ht' := renameInto ht j Theta hj
 simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs' hv' hr' ht'
 apply zeroSuccessorCases Theta (code.relabel j) _
 ·
   have he : Nonempty (Derivation body (eqn (code.relabel j) z :: Theta) (eqn (code.relabel j) z)) :=
     ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hd := RankCalibrationLeafProof.variableZero (input.relabel j) typ raw field (rank.relabel j) hp hc hr'
   obtain ⟨he⟩ := he
   exact headTransport RankMemoDefinitions.decoder (rank.relabel j) z (code.relabel j) Fin.elim0
     ⟨symm he⟩ (withHyp hd _)
 · intro beta' k Xi stage hk he
   rw [graph1Rename]
   have hs'' := renameInto hs' k Xi hk
   have hv'' := renameInto hv' k Xi hk
   have hr'' := renameInto hr' k Xi hk
   have ht'' := renameInto ht' k Xi hk
   have hp' := renameInto hp k Xi hk
   have hc' := renameInto hc k Xi hk
   simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs'' hv'' hr'' ht'' hp' hc'
   have hev := outputTransport (OriginalHereditaryEvaluatorDefinitions.evaluator R)
     ((code.relabel j).relabel k) (suc stage) (![(input.relabel j).relabel k,(parameter.relabel j).relabel k]) he hv''
   have hd := RankCalibrationBaseSuccessorProof.variable R H G M W stage ((input.relabel j).relabel k)
     ((parameter.relabel j).relabel k) (typ.relabel k) (raw.relabel k) (field.relabel k) ((rank.relabel j).relabel k)
     hs'' hev hr'' hp' hc' ht''
   obtain ⟨he⟩ := he
   exact headTransport RankMemoDefinitions.decoder ((rank.relabel j).relabel k) (suc stage) ((code.relabel j).relabel k)
     Fin.elim0 ⟨symm he⟩ hd

theorem actualBottom : RankCalibrationBaseTargets.ActualBottom := by
 intro R H G M W body alpha Delta input parameter code rank hs hv hr ht
 apply RankCalibrationBaseFieldsProof.leafCases 3 input _ ht
 intro beta j Theta typ raw field hj hp hc
 rw [graph1Rename]
 have hs' := renameInto hs j Theta hj
 have hv' := renameInto hv j Theta hj
 have hr' := renameInto hr j Theta hj
 have ht' := renameInto ht j Theta hj
 simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs' hv' hr' ht'
 apply zeroSuccessorCases Theta (code.relabel j) _
 ·
   have he : Nonempty (Derivation body (eqn (code.relabel j) z :: Theta) (eqn (code.relabel j) z)) :=
     ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hn := RankCalibrationBaseNonzeroProof.actualNonvariableNonzero R H G M W body beta Theta
     (input.relabel j) (parameter.relabel j) (code.relabel j) 2 hs' hv' ht'
   simp only [equalEqn] at hn
   obtain ⟨hn⟩ := withHyp hn (eqn (code.relabel j) z)
   obtain ⟨he⟩ := he
   exact ⟨Derivation.explosion (Derivation.implicationElimination hn he)⟩
 · intro beta' k Xi stage hk he
   rw [graph1Rename]
   have hs'' := renameInto hs' k Xi hk
   have hv'' := renameInto hv' k Xi hk
   have hr'' := renameInto hr' k Xi hk
   have ht'' := renameInto ht' k Xi hk
   have hp' := renameInto hp k Xi hk
   have hc' := renameInto hc k Xi hk
   simp only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs'' hv'' hr'' ht'' hp' hc'
   have hev := outputTransport (OriginalHereditaryEvaluatorDefinitions.evaluator R)
     ((code.relabel j).relabel k) (suc stage) (![(input.relabel j).relabel k,(parameter.relabel j).relabel k]) he hv''
   have hd := RankCalibrationBaseSuccessorProof.bottom R H G M W stage ((input.relabel j).relabel k)
     ((parameter.relabel j).relabel k) (typ.relabel k) (raw.relabel k) (field.relabel k) ((rank.relabel j).relabel k)
     hs'' hev hr'' hp' hc' ht''
   obtain ⟨he⟩ := he
   exact headTransport RankMemoDefinitions.decoder ((rank.relabel j).relabel k) (suc stage) ((code.relabel j).relabel k)
     Fin.elim0 ⟨symm he⟩ hd
theorem actualNonvariableNonzero : RankCalibrationBaseTargets.ActualNonvariableNonzero :=
 RankCalibrationBaseNonzeroProof.actualNonvariableNonzero
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseProof
