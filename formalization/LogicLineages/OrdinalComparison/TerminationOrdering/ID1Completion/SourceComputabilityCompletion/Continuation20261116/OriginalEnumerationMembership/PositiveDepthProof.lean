module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.OrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.PositiveDepthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115 DepthSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalApplicationCertificateConstructorsSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Auxiliary simultaneous totality queries only; the depth program is unchanged. -/
def queries (n : Nat) : Fin 2 → Program 2 :=
  ![OriginalEnumerationDepth.Equation.answers n,
    .composition OriginalEnumerationDepth.collect (fun _ => OriginalEnumerationDepth.Equation.answers n)]

theorem cases (n : Nat) (raw : OTerm alpha) (psi : Formula alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (maximum : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 (OriginalEnumerationDepth.depth n) (suc maximum) (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (queries n) ![raw,z] psi
  intro beta j ys Theta hj hq
  have hx : (fun i => (![raw,z] i).relabel j) = ![raw.relabel j,z] := by
    funext i
    fin_cases i
    · rfl
    · change (z : OTerm alpha).relabel j = (z : OTerm beta)
      exact zRelabel j
  rw [hx] at hq
  have hvj := renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hvj
  have ha : Nonempty (Derivation body Theta (graph2 (OriginalEnumerationDepth.Equation.answers n) (ys 0) (raw.relabel j) z)) := hq 0
  have hc := unaryRecover OriginalEnumerationDepth.collect (OriginalEnumerationDepth.Equation.answers n)
    (ys 1) (ys 0) ![raw.relabel j,z] (hq 1) ha
  exact next beta j Theta (ys 1) hj (OriginalEnumerationDepth.ValueProof.atAnswers n (raw.relabel j) (ys 0) (ys 1) hvj ha hc)

theorem zeroImpossible (n : Nat) (raw : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw)))
    (hb : Nonempty (Derivation body Delta (Targets.depthBound n raw z))) :
    Nonempty (Derivation body Delta ⊥) := by
  apply cases n raw _ hv
  intro beta j Theta maximum hj hd
  have hbj := renameInto hb j Theta hj
  simp only [boundRename,zRelabel] at hbj
  have hlt := DepthBoundProof.observedBound n (raw.relabel j) z (suc maximum) hd hbj
  obtain ⟨hlt⟩ := OrderProof.successorBackward maximum z hlt
  obtain ⟨hn⟩ := InternalApplicationValidityStackAppendTransitionProof.notLessZero
    (body := body) (Gamma := Theta) maximum
  exact ⟨Derivation.implicationElimination hn hlt⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.PositiveDepthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.PositiveDepthProof
