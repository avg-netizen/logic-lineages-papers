module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetDepthSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionSmallIndexProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetDepthCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetDepthQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalOriginalPairingOrderArithmeticProof (weakTransport)
open InternalQuotientComparisonProof (equalToNext)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalHereditaryBudgetDepthSyntaxProof
open OriginalHereditaryFuelProgram (budget)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalSquareRootArithmeticSupportProof (orderLeft orderRight)
open InternalMultiplicationLawsProof (mul)
open InternalPairingSumBoundsArithmeticProof (successorWeak)
open OriginalContextInsertionBelowCoreProof (successorStrict)

open OriginalHereditaryBudgetDepthCoreProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
theorem successorKnown (depth lower c v w : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row depth)))
 (hb : Nonempty (Derivation body Delta (ltF (suc lower) (suc (suc depth)))))
 (hv : Nonempty (Derivation body Delta (graph2 budget v (suc lower) c)))
 (hw : Nonempty (Derivation body Delta (graph2 budget w (suc depth) c))) :
 Nonempty (Derivation body Delta (result v w)) := by
 let qs : Fin 2 → Program 3 := ![
   .composition budget ![.projection 0,.projection 2],
   .composition budget ![.projection 1,.projection 2] ]
 let xs : Fin 3 → OTerm alpha := Fin.cons lower (Fin.cons depth (Fin.cons c Fin.elim0))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 let xx : Fin 3 → OTerm beta := Fin.cons (lower.relabel j) (Fin.cons (depth.relabel j) (Fin.cons (c.relabel j) Fin.elim0))
 have hq' : ∀ i, Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
   intro i
   simpa only [xs,xx,consTermRename,emptyRename] using hq i
 have hp := binaryRecover budget (.projection 0) (.projection 2) (ys 0) (lower.relabel j) (c.relabel j) xx
   (hq' 0) (projectionValue 0 xx) (projectionValue 2 xx)
 have hqv := binaryRecover budget (.projection 1) (.projection 2) (ys 1) (depth.relabel j) (c.relabel j) xx
   (hq' 1) (projectionValue 1 xx) (projectionValue 2 xx)
 have hi' := renameInto hi j Theta hj
 rw [rowRename] at hi'
 have hb' := renameInto hb j Theta hj
 have hv' := renameInto hv j Theta hj
 have hw' := renameInto hw j Theta hj
 simp only [orderRename,sucRelabel,graph2Rename] at hb' hv' hw'
 rw [resultRename]
 exact atSuccessors (depth.relabel j) (lower.relabel j) (c.relabel j) (v.relabel j) (w.relabel j)
   (ys 0) (ys 1) hi' hb' hp hqv hv' hw'

theorem zeroKnown (depth c v w : OTerm alpha)
 (hv : Nonempty (Derivation body Delta (graph2 budget v z c)))
 (hw : Nonempty (Derivation body Delta (graph2 budget w (suc depth) c))) :
 Nonempty (Derivation body Delta (result v w)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons depth (Fin.cons c Fin.elim0)
 apply InternalAcceptanceSupportProof.programCases budget xs _
 intro beta j Theta previous hj hp
 let xx : Fin 2 → OTerm beta := Fin.cons (depth.relabel j) (Fin.cons (c.relabel j) Fin.elim0)
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hp
 have hv' := renameInto hv j Theta hj
 have hw' := renameInto hw j Theta hj
 simp only [graph2Rename,sucRelabel,zRelabel] at hv' hw'
 rw [resultRename]
 exact zeroLower (depth.relabel j) (c.relabel j) (v.relabel j) (w.relabel j) previous hv' hp hw'

theorem succCore (depth b c v w : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row depth)))
 (hf : Nonempty (Derivation body Delta (fields (suc depth) b c v w))) :
 Nonempty (Derivation body Delta (result v w)) := by
 apply zeroSuccessorCases Delta b _
 · have hf' := withHyp hf (eqn b z)
   have hv := headTransport budget v b z (Fin.cons c Fin.elim0)
     ⟨Derivation.hypothesis List.mem_cons_self⟩ (andLeft (andRight hf'))
   exact zeroKnown depth c v w hv (andRight (andRight hf'))
 · intro beta j Theta lower hj he
   have hi' := renameInto hi j Theta hj
   rw [rowRename] at hi'
   have hf' := renameInto hf j Theta hj
   simp only [fieldsRename,sucRelabel] at hf'
   have hb : Nonempty (Derivation body Theta (ltF (suc lower) (suc (suc (depth.relabel j))))) := by
     obtain ⟨he⟩ := he
     obtain ⟨h⟩ := andLeft hf'
     exact ⟨orderLeft _ he h⟩
   have hv := headTransport budget (v.relabel j) (b.relabel j) (suc lower) (Fin.cons (c.relabel j) Fin.elim0)
     he (andLeft (andRight hf'))
   rw [resultRename]
   exact successorKnown (depth.relabel j) lower (c.relabel j) (v.relabel j) (w.relabel j)
     hi' hb hv (andRight (andRight hf'))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetDepthQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetDepthQueryProof
