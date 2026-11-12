module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootCompletionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc)
open InternalTagArithmeticSupportProof (symm congSuc)
open InternalOriginalOrderSyntaxProof (ltF)
open InternalSquareRootArithmeticSupportProof (orderRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem branchBound (job weight B : OTerm alpha)
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (hb : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.branching B job))) :
 Nonempty (Derivation body Delta (ltF (suc (suc weight)) (suc B))) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
 have h1 := unaryValue .succ OriginalHereditaryFuelProgram.weight (suc weight) weight xs (successorValue (Fin.cons weight Fin.elim0)) hw
 have h2 : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.branching (suc (suc weight)) job)) :=
  unaryValue .succ (OriginalRawSyntaxTransport.succOf OriginalHereditaryFuelProgram.weight) (suc (suc weight)) (suc weight) xs
    (successorValue (Fin.cons (suc weight) Fin.elim0)) h1
 have he := valueUnique OriginalHereditaryFuelProgram.branching (suc (suc weight)) B (Fin.cons job Fin.elim0) h2 hb
 exact ⟨orderRight (suc (suc weight)) (congSuc (Classical.choice he))
   (Classical.choice (InternalCoprimeMultipleBoundedProof.selfLtSucc (body:=body) (Gamma:=Delta) (suc (suc weight))))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySourceRootBranchProof
