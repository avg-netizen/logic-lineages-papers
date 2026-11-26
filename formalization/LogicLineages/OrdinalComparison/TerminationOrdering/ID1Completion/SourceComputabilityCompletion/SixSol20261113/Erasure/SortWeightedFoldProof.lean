module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedFoldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRawListRecursion
open InternalRawListRecursionSyntaxProof InternalRawListRecursionProof
open InternalTagArithmeticSyntaxProof (emb z eqn)
open InternalAdditionLawsProof (add)
open InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SortWeightedDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem stepValue {k : Nat} (F : Program (k+1))
 (head result weight : OTerm alpha) (params : Fin k → OTerm alpha)
 (hh : Nonempty (Derivation body Delta (programGraph F weight (Fin.cons head params)))) :
 Nonempty (Derivation body Delta (programGraph (step F) (add weight result)
   (Fin.cons head (Fin.cons result params)))) := by
 apply compositionValue InternalArithmeticPrograms.addition
   ![.composition F (Fin.cons (.projection 0) (fun i : Fin k => .projection i.succ.succ)), .projection 1]
   (add weight result) (Fin.cons head (Fin.cons result params)) ![weight,result]
   (InternalArithmeticProgramsSupportProof.additionValue weight result)
 intro i
 refine Fin.cases ?_ (Fin.cases ?_ (fun q => Fin.elim0 q)) i
 · exact InternalListMapProof.mapHeadValue F head result weight params hh
 · exact projectionValue (1 : Fin (k+2)) (Fin.cons head (Fin.cons result params))

theorem nilValue {k : Nat} (F : Program (k+1)) (params : Fin k → OTerm alpha) :
 Nonempty (Derivation body Delta (programGraph (weighted F) z (Fin.cons z params))) :=
 InternalRawListRecursionProof.nilValue InternalRawListRecursion.zero (step F) z params
   (InternalAcceptanceConjunctionProof.constantZeroValue params)

theorem consValue {k : Nat} (F : Program (k+1))
 (code head tail weight sum : OTerm alpha) (params : Fin k → OTerm alpha)
 (hc : Nonempty (Derivation body Delta (programGraph InternalListCodec.consCode code ![head,tail])))
 (hh : Nonempty (Derivation body Delta (programGraph F weight (Fin.cons head params))))
 (ht : Nonempty (Derivation body Delta (programGraph (weighted F) sum (Fin.cons tail params)))) :
 Nonempty (Derivation body Delta (programGraph (weighted F) (add weight sum) (Fin.cons code params))) := by
 obtain ⟨hs⟩ := stepValue F head sum weight params hh
 obtain ⟨ht⟩ := ht
 have hex : Nonempty (Derivation body Delta
     (consStep InternalRawListRecursion.zero (step F) (add weight sum) head tail params)) := by
   apply Nonempty.intro
   apply Derivation.existentialIntroduction (emb sum)
   rw [consStepInstance]
   exact Derivation.conjunctionIntroduction ht hs
 obtain ⟨heq⟩ := closedApply
   (actualOriginalListRecursionCons body k InternalRawListRecursion.zero (step F)
     alpha code head tail (add weight sum) params) hc
 obtain ⟨hex⟩ := hex
 exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight heq) hex⟩

theorem consUnique {k : Nat} (F : Program (k+1))
 (code head tail weight sum out : OTerm alpha) (params : Fin k → OTerm alpha)
 (hc : Nonempty (Derivation body Delta (programGraph InternalListCodec.consCode code ![head,tail])))
 (hh : Nonempty (Derivation body Delta (programGraph F weight (Fin.cons head params))))
 (ht : Nonempty (Derivation body Delta (programGraph (weighted F) sum (Fin.cons tail params))))
 (ho : Nonempty (Derivation body Delta (programGraph (weighted F) out (Fin.cons code params)))) :
 Nonempty (Derivation body Delta (eqn out (add weight sum))) :=
 valueUnique (weighted F) out (add weight sum) (Fin.cons code params) ho
   (consValue F code head tail weight sum params hc hh ht)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedFoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.SortWeightedFoldProof
