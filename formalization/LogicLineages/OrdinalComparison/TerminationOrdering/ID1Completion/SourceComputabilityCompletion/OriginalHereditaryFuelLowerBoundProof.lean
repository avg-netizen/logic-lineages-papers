module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomFuelTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetDepthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCellsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRootPotentialProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelLowerBoundProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (trans symm congSuc addSucc addZero)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open InternalSquareRootArithmeticSupportProof (orderLeft orderRight)
open InternalOriginalPairingOrderArithmeticProof (addWeakBoth)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualLowerBound (parent fuel : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.fuel fuel parent))) :
 Nonempty (Derivation body Delta (ltF (suc (suc z)) (suc fuel))) := by
 let budgetP : Program 1 := .composition OriginalHereditaryFuelProgram.budget ![OriginalHereditaryFuelProgram.weight,OriginalHereditaryFuelProgram.branching]
 let qs : Fin 3 → Program 1 := ![OriginalHereditaryFuelProgram.weight,OriginalHereditaryFuelProgram.branching,budgetP]
 let xs : Fin 1 → OTerm alpha := Fin.cons parent Fin.elim0
 apply queryCases qs xs _
 intro beta j ys Theta hj hq
 simp only [orderRename,sucRelabel,zRelabel]
 let xx : Fin 1 → OTerm beta := Fin.cons (parent.relabel j) Fin.elim0
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 have hf' := renameInto hf j Theta hj
 rw [graph1Rename] at hf'
 have hb := binaryRecover OriginalHereditaryFuelProgram.budget OriginalHereditaryFuelProgram.weight OriginalHereditaryFuelProgram.branching
   (ys 2) (ys 0) (ys 1) xx (hq 2) (hq 0) (hq 1)
 have hone := OriginalHereditaryBudgetDepthProof.actualMonotone body beta Theta (ys 0) z (ys 1) (suc z) (ys 2)
   (OriginalHereditaryBudgetSumBoundCellsProof.zeroBound (ys 0))
   (OriginalHereditaryBudgetInternalProof.actualZero body beta Theta (ys 1)) hb
 have hd := addWeakBoth (suc z) (ys 2) (suc z) (ys 2) hone hone
 have hmul := binaryRecover InternalArithmeticPrograms.multiplication (OriginalRawSyntaxTransport.constant 1 2) budgetP
   (fuel.relabel j) (suc (suc z)) (ys 2) xx hf' (constantValue 2 xx) (hq 2)
 have hdouble : Nonempty (Derivation body Theta (graph2 InternalArithmeticPrograms.multiplication (add (ys 2) (ys 2)) (suc (suc z)) (ys 2))) :=
   outputTransport InternalArithmeticPrograms.multiplication _ _ (Fin.cons (suc (suc z)) (Fin.cons (ys 2) Fin.elim0))
     ⟨OriginalHereditaryInternalWeightArithmeticProof.twoMul (ys 2)⟩
     (InternalArithmeticProgramsMultiplicationProof.multiplicationValue (suc (suc z)) (ys 2))
 have he := valueUnique InternalArithmeticPrograms.multiplication (add (ys 2) (ys 2)) (fuel.relabel j)
   (Fin.cons (suc (suc z)) (Fin.cons (ys 2) Fin.elim0)) hdouble hmul
 exact ⟨orderRight (suc (suc z)) (congSuc (Classical.choice he))
   (orderLeft (suc (add (ys 2) (ys 2))) (trans (addSucc (suc z) z) (congSuc (addZero (suc z)))) (Classical.choice hd))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelLowerBoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelLowerBoundProof
