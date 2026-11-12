module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAdjacentSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open OriginalNumericListSort OriginalTypedArgumentObservationsAccumulatorQueryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] sort OriginalNumericListSort.insert

theorem unaryCases (P : Program 1) (input : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (out : OTerm beta),
  (∀ f ∈ Delta, f.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (graph1 P out (input.relabel j))) →
  Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 apply programCases P (Fin.cons input Fin.elim0) psi
 intro beta j Theta out hj ho
 have hv : (fun i : Fin 1 => ((Fin.cons input Fin.elim0 : Fin 1 → OTerm alpha) i).relabel j) =
   Fin.cons (input.relabel j) Fin.elim0 := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hv] at ho
 exact next beta j Theta out hj ho

theorem sortConsRecover (code head tail sorted out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
 (hr : Nonempty (Derivation body Delta (graph1 sort sorted tail)))
 (ho : Nonempty (Derivation body Delta (graph1 sort out code))) :
 Nonempty (Derivation body Delta (graph2 insert out sorted head)) := by
 apply binaryCases insert sorted head _
 intro beta j Theta actual hj hi
 rw [graph2Rename]
 have hc' := renameInto hc j Theta hj
 have hr' := renameInto hr j Theta hj
 have ho' := renameInto ho j Theta hj
 rw [graph2Rename] at hc'
 rw [graph1Rename] at hr' ho'
 have ha := OriginalNumericListSortValueProof.sortCons (code.relabel j) (head.relabel j)
   (tail.relabel j) (sorted.relabel j) actual hc' hr' hi
 have he := valueUnique sort actual (out.relabel j) (Fin.cons (code.relabel j) Fin.elim0) ha ho'
 exact outputTransport insert actual (out.relabel j)
   (Fin.cons (sorted.relabel j) (Fin.cons (head.relabel j) Fin.elim0)) he hi

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAdjacentSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortAdjacentSupportProof
