module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineExpansionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersFieldQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineExpansionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem cutoffChoiceRename {beta : Type} (rank : Bool) (yes no : OTerm alpha) (j : alpha → beta) :
    (if rank then yes else no).relabel j = if rank then yes.relabel j else no.relabel j := by
  cases rank <;> rfl

/-- Select the shared child and both literal binder-sensitive cutoff values
inside one actual existential block. -/
theorem unaryFieldCases (raw k otherK : OTerm alpha) (psi : Formula alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (child childK otherChildK : OTerm beta),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (firstOf (.projection 0)) child (raw.relabel j))) →
      Nonempty (Derivation body Theta (graph2 nextCutoff childK (k.relabel j) (raw.relabel j))) →
      Nonempty (Derivation body Theta (graph2 nextCutoff otherChildK (otherK.relabel j) (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let qs : Fin 3 → Program 3 := ![
    (.composition (firstOf (.projection 0)) (fun _ : Fin 1 => .projection 0)),
    (.composition nextCutoff ![.projection 1,.projection 0]),
    (.composition nextCutoff ![.projection 2,.projection 0])]
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons k (Fin.cons otherK Fin.elim0))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  let xx : Fin 3 → OTerm beta := fun i => (xs i).relabel j
  exact step beta j Theta (ys 0) (ys 1) (ys 2) hj
    (unaryRecover (firstOf (.projection 0)) (.projection 0) (ys 0) (raw.relabel j) xx
      (hq 0) (projectionValue 0 xx))
    (binaryRecover nextCutoff (.projection 1) (.projection 0) (ys 1) (k.relabel j) (raw.relabel j) xx
      (hq 1) (projectionValue 1 xx) (projectionValue 0 xx))
    (binaryRecover nextCutoff (.projection 2) (.projection 0) (ys 2) (otherK.relabel j) (raw.relabel j) xx
      (hq 2) (projectionValue 2 xx) (projectionValue 0 xx))

theorem binaryFieldCases (raw : OTerm alpha) (psi : Formula alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (first second : OTerm beta),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (firstOf (.projection 0)) first (raw.relabel j))) →
      Nonempty (Derivation body Theta (graph1 (secondOf (.projection 0)) second (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let qs : Fin 2 → Program 1 := ![firstOf (.projection 0),secondOf (.projection 0)]
  apply queryCases qs (Fin.cons raw Fin.elim0) _
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  exact step beta j Theta (ys 0) (ys 1) hj (hq 0) (hq 1)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersFieldQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersFieldQueriesProof
