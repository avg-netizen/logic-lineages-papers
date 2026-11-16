module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.RankStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.InputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (queryCases andIntro)
open Continuation20261114.HeadWindowBooleanRange
open Continuation20261114.HeadWindowBooleanRange.InductionSyntaxProof (booleanRename)
open SyntaxProof BindingProof InputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem extractRange (n : Nat) (key param out : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph2 (extract n) out key param))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply programCases rank (Fin.cons key (Fin.cons param Fin.elim0)) _
  intro beta j Theta parentRank hj hr
  rw [booleanRename]
  simp only [consTermRename,emptyRename] at hr
  have hej := renameInto he j Theta hj
  rw [graph2Rename] at hej
  exact atRankApply n parentRank (key.relabel j) (param.relabel j) (out.relabel j)
    (rankInduction n parentRank (fun _ _ r ih => RankStepProof.step n r ih)) (andIntro hr hej)

theorem fieldsRange (n : Nat) (xs : Fin 6 → OTerm alpha) (out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (programGraph (fields n) out xs))) :
    Nonempty (Derivation body Delta (BooleanValue out)) := by
  apply queryCases ![keyQuery,parameterQuery] xs _
  intro beta j ys Theta hj hg
  rw [booleanRename]
  have hfj := renameInto hf j Theta hj
  rw [programRename] at hfj
  have hk : Nonempty (Derivation body Theta (programGraph keyQuery (ys 0) (fun i => (xs i).relabel j))) := hg 0
  have hp : Nonempty (Derivation body Theta (programGraph parameterQuery (ys 1) (fun i => (xs i).relabel j))) := hg 1
  exact extractRange n (ys 0) (ys 1) (out.relabel j)
    (extractFromFields n (fun i => (xs i).relabel j) (ys 0) (ys 1) (out.relabel j) hk hp hfj)

theorem internalBoolean : Targets.InternalBoolean := by
  intro n body alpha Delta xs out hf
  exact fieldsRange n xs out hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.Proof
