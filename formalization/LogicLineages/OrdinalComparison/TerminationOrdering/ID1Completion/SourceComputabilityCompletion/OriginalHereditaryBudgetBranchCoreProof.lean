module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetBranchSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetBranchCoreProof
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
open OriginalHereditaryBudgetBranchSyntaxProof
open OriginalHereditaryFuelProgram (budget)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (b c v w : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z b c v w))) :
 Nonempty (Derivation body Delta (result v w)) := by
 have hv := valueUnique budget v (suc z) (Fin.cons z (Fin.cons b Fin.elim0))
   (andLeft (andRight hf)) (OriginalHereditaryBudgetInternalProof.actualZero body alpha Delta b)
 have hw := valueUnique budget w (suc z) (Fin.cons z (Fin.cons c Fin.elim0))
   (andRight (andRight hf)) (OriginalHereditaryBudgetInternalProof.actualZero body alpha Delta c)
 exact weakTransport v w (suc z) (suc z) hv hw ⟨equalToNext (InternalTagArithmeticSupportProof.refl (suc z))⟩

theorem succCore (depth b c v w : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row depth)))
 (hf : Nonempty (Derivation body Delta (fields (suc depth) b c v w))) :
 Nonempty (Derivation body Delta (result v w)) := by
 let qs : Fin 2 → Program 3 := ![
   .composition budget ![.projection 0,.projection 1],
   .composition budget ![.projection 0,.projection 2] ]
 let xs : Fin 3 → OTerm alpha := Fin.cons depth (Fin.cons b (Fin.cons c Fin.elim0))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 let xx : Fin 3 → OTerm beta := Fin.cons (depth.relabel j) (Fin.cons (b.relabel j) (Fin.cons (c.relabel j) Fin.elim0))
 have hq' : ∀ i, Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
   intro i
   simpa only [xs,xx,consTermRename,emptyRename] using hq i
 have hp := binaryRecover budget (.projection 0) (.projection 1) (ys 0) (depth.relabel j) (b.relabel j) xx
   (hq' 0) (projectionValue 0 xx) (projectionValue 1 xx)
 have hqv := binaryRecover budget (.projection 0) (.projection 2) (ys 1) (depth.relabel j) (c.relabel j) xx
   (hq' 1) (projectionValue 0 xx) (projectionValue 2 xx)
 have hi' := renameInto hi j Theta hj
 rw [rowRename] at hi'
 have hf' := renameInto hf j Theta hj
 simp only [fieldsRename,sucRelabel] at hf'
 have hprevious := rowApply (depth.relabel j) (b.relabel j) (c.relabel j) (ys 0) (ys 1)
   hi' (andIntro (andLeft hf') (andIntro hp hqv))
 have hv := OriginalHereditaryBudgetInternalProof.actualSuccessorEquation body beta Theta
   (depth.relabel j) (b.relabel j) (ys 0) (v.relabel j) hp (andLeft (andRight hf'))
 have hw := OriginalHereditaryBudgetInternalProof.actualSuccessorEquation body beta Theta
   (depth.relabel j) (c.relabel j) (ys 1) (w.relabel j) hqv (andRight (andRight hf'))
 rw [resultRename]
 exact weakTransport _ _ _ _ hv hw (OriginalHereditaryBudgetOrderArithmeticProof.stepWeak
   (b.relabel j) (c.relabel j) (ys 0) (ys 1) (andLeft hf') hprevious)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetBranchCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetBranchCoreProof
