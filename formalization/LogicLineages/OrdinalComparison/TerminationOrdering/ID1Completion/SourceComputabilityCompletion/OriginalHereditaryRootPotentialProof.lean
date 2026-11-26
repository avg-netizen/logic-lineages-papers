module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRootPotentialTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsMultiplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRootPotentialProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel)
open InternalTagArithmeticSupportProof (symm trans addZero)
open InternalAdditionLawsProof (add)
open OriginalHereditaryInternalWeightArithmeticProof (twoMul)
open InternalArithmeticProgramsMultiplicationProof (multiplicationValue)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem actualInitialPotential : OriginalHereditaryRootPotentialTargets.ActualInitialPotential := by
 intro body alpha Delta parent visit work branching fuel hv hw hb hf
 let budgetP : Program 1 := .composition OriginalHereditaryFuelProgram.budget ![OriginalHereditaryFuelProgram.weight,OriginalHereditaryFuelProgram.branching]
 let qs : Fin 2 → Program 1 := ![OriginalHereditaryFuelProgram.weight,budgetP]
 let xs : Fin 1 → OTerm alpha := Fin.cons parent Fin.elim0
 apply queryCases qs xs _
 intro beta j ys Theta hj hq
 rw [graph2Rename]
 let xx : Fin 1 → OTerm beta := Fin.cons (parent.relabel j) Fin.elim0
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 have hv' := renameInto hv j Theta hj
 have hw' := renameInto hw j Theta hj
 have hb' := renameInto hb j Theta hj
 have hf' := renameInto hf j Theta hj
 simp only [graph1Rename,graph2Rename,zRelabel] at hv' hw' hb' hf'
 have hbudget := binaryRecover OriginalHereditaryFuelProgram.budget OriginalHereditaryFuelProgram.weight OriginalHereditaryFuelProgram.branching
   (ys 1) (ys 0) (branching.relabel j) xx (hq 1) (hq 0) hb'
 let args : Fin 2 → OTerm beta := Fin.cons (parent.relabel j) (Fin.cons (branching.relabel j) Fin.elim0)
 have hweight := unaryValue OriginalHereditaryFuelProgram.weight (.projection 0) (ys 0) (parent.relabel j) args (hq 0) (projectionValue 0 args)
 have hjob : Nonempty (Derivation body Theta (graph2 OriginalHereditaryBudgetSum.jobBudget (ys 1) (parent.relabel j) (branching.relabel j))) :=
  binaryValue OriginalHereditaryFuelProgram.budget (.composition OriginalHereditaryFuelProgram.weight (fun _ : Fin 1 => .projection 0)) (.projection 1)
   (ys 1) (ys 0) (branching.relabel j) args hbudget hweight (projectionValue 1 args)
 have hcost := OriginalHereditaryAgendaPotentialFrameProof.visitCost (visit.relabel j) (parent.relabel j) (branching.relabel j) (ys 1) hv' hjob
 have hsum := OriginalHereditaryAgendaPotentialRecurrenceProof.consValue (work.relabel j) (visit.relabel j) z (branching.relabel j) (add (ys 1) (ys 1)) z hw' hcost
  (OriginalHereditaryAgendaPotentialRecurrenceProof.nilValue (branching.relabel j))
 have hsum' := outputTransport OriginalHereditaryAgendaPotential.agenda (add (add (ys 1) (ys 1)) z) (add (ys 1) (ys 1))
   (Fin.cons (work.relabel j) (Fin.cons (branching.relabel j) Fin.elim0)) (Nonempty.intro (addZero _)) hsum
 have hmul := binaryRecover InternalArithmeticPrograms.multiplication (OriginalRawSyntaxTransport.constant 1 2) budgetP
   (fuel.relabel j) (suc (suc z)) (ys 1) xx hf' (constantValue 2 xx) (hq 1)
 have hdbl : Nonempty (Derivation body Theta (graph2 InternalArithmeticPrograms.multiplication (add (ys 1) (ys 1)) (suc (suc z)) (ys 1))) := outputTransport InternalArithmeticPrograms.multiplication _ (add (ys 1) (ys 1))
   (Fin.cons (suc (suc z)) (Fin.cons (ys 1) Fin.elim0)) (Nonempty.intro (twoMul (ys 1))) (multiplicationValue (suc (suc z)) (ys 1))
 have he := valueUnique InternalArithmeticPrograms.multiplication (fuel.relabel j) (add (ys 1) (ys 1))
   (Fin.cons (suc (suc z)) (Fin.cons (ys 1) Fin.elim0)) hmul hdbl
 exact outputTransport OriginalHereditaryAgendaPotential.agenda (add (ys 1) (ys 1)) (fuel.relabel j)
   (Fin.cons (work.relabel j) (Fin.cons (branching.relabel j) Fin.elim0)) (Nonempty.intro (symm (Classical.choice he))) hsum'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRootPotentialProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRootPotentialProof
