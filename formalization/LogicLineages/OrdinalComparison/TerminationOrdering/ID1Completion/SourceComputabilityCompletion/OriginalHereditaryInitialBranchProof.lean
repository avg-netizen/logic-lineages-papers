module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInitialBranchTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInitialJobProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInitialBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc)
open InternalOriginalOrderSyntaxProof (ltF)
open InternalQuotientComparisonProof (equalToNext)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem branchBound (job weight B : OTerm alpha)
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (hb : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.branching B job))) :
 Nonempty (Derivation body Delta (ltF (suc (suc weight)) (suc B))) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
 have h1 := unaryValue .succ OriginalHereditaryFuelProgram.weight (suc weight) weight xs
   (successorValue (Fin.cons weight Fin.elim0)) hw
 have h2 : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.branching (suc (suc weight)) job)) :=
   unaryValue .succ (OriginalRawSyntaxTransport.succOf OriginalHereditaryFuelProgram.weight)
     (suc (suc weight)) (suc weight) xs (successorValue (Fin.cons (suc weight) Fin.elim0)) h1
 exact ⟨equalToNext (Classical.choice (valueUnique OriginalHereditaryFuelProgram.branching (suc (suc weight)) B xs h2 hb))⟩
theorem actualJob : OriginalHereditaryInitialBranchTargets.ActualJob := by
 intro body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job weight B hp hc hr ht hj hs hw hb
 exact OriginalHereditaryInitialJobProof.actualJob body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job weight B
   hp hc hr ht hj hs hw (branchBound job weight B hw hb)
theorem actualAgenda : OriginalHereditaryInitialBranchTargets.ActualAgenda := by
 intro body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job weight B visit work hp hc hr ht hj hs hw hb hv hwork
 exact OriginalHereditaryInitialJobProof.actualAgenda body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job weight B visit work
   hp hc hr ht hj hs hw (branchBound job weight B hw hb) hv hwork
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInitialBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInitialBranchProof
