module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WrapperProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WrapperCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem cases (n : Nat) (labels heads types bases tuples extras out : OTerm alpha) (psi : Formula alpha)
    (hv : Nonempty (Derivation body Delta (programGraph (branch n) out ![labels,heads,types,bases,tuples,extras])))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (mappedHeads : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (convertedHeads n) mappedHeads (heads.relabel j))) →
      Nonempty (Derivation body Theta (programGraph OriginalNumberedEnumerationBranch.branch (out.relabel j)
        ![labels.relabel j,mappedHeads,types.relabel j,bases.relabel j,tuples.relabel j,extras.relabel j])) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases (convertedHeads n) (Fin.cons heads Fin.elim0) psi
  intro beta j Theta mappedHeads hj hm
  simp only [consTermRename,emptyRename] at hm
  have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [programRename] at hvj
  have hx : (fun i => (![labels,heads,types,bases,tuples,extras] i).relabel j) =
      ![labels.relabel j,heads.relabel j,types.relabel j,bases.relabel j,tuples.relabel j,extras.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hvj
  exact next beta j Theta mappedHeads hj hm
    (WrapperProof.recover n (labels.relabel j) (heads.relabel j) (types.relabel j) (bases.relabel j)
      (tuples.relabel j) (extras.relabel j) (out.relabel j) mappedHeads hvj hm)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WrapperCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.WrapperCasesProof
