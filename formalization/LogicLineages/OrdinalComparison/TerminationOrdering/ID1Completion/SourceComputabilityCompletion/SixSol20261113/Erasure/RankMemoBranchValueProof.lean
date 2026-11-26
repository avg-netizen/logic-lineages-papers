module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoWeightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoBranchValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open RankMemoDefinitions ObservationDescentDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem directValue (slot : DirectSlot) (stage tab data typed rank : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 payload data stage tab)))
 (hs : Nonempty (Derivation body Delta (graph1 (select (directPath slot)) typed data)))
 (hw : Nonempty (Derivation body Delta (programGraph lookupWeight rank
   (Fin.cons typed (Fin.cons stage (Fin.cons tab Fin.elim0)))))) :
 Nonempty (Derivation body Delta (graph2 (directRank slot) rank stage tab)) := by
 let xs : Fin 2 → OTerm alpha := ![stage,tab]
 have ht := unaryValue (select (directPath slot)) payload typed data xs hs hp
 apply compositionValue lookupWeight ![typedAt slot,.projection 0,.projection 1]
   rank xs (Fin.cons typed (Fin.cons stage (Fin.cons tab Fin.elim0))) hw
 intro i
 exact Fin.cases ht (Fin.cases (projectionValue 0 xs)
   (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i

theorem rowValue (slot : ListSlot) (stage tab data row rank : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 payload data stage tab)))
 (hs : Nonempty (Derivation body Delta (graph1 (select (listPath slot)) row data)))
 (hw : Nonempty (Derivation body Delta (programGraph (SortWeightedDefinitions.weighted lookupWeight) rank
   (Fin.cons row (Fin.cons stage (Fin.cons tab Fin.elim0)))))) :
 Nonempty (Derivation body Delta (graph2 (rowRank slot) rank stage tab)) := by
 let xs : Fin 2 → OTerm alpha := ![stage,tab]
 have ht := unaryValue (select (listPath slot)) payload row data xs hs hp
 apply compositionValue (SortWeightedDefinitions.weighted lookupWeight) ![rowAt slot,.projection 0,.projection 1]
   rank xs (Fin.cons row (Fin.cons stage (Fin.cons tab Fin.elim0))) hw
 intro i
 exact Fin.cases ht (Fin.cases (projectionValue 0 xs)
   (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k))) i

theorem sumValue (a b : Program 2) (stage tab x y : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph2 a x stage tab)))
 (hb : Nonempty (Derivation body Delta (graph2 b y stage tab))) :
 Nonempty (Derivation body Delta (graph2 (sum a b) (InternalAdditionLawsProof.add x y) stage tab)) :=
 binaryValue InternalArithmeticPrograms.addition a b (InternalAdditionLawsProof.add x y) x y
   (![stage,tab] : Fin 2 → OTerm alpha)
   (InternalArithmeticProgramsSupportProof.additionValue x y) ha hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoBranchValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoBranchValueProof
