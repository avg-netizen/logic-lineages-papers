module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Supply one original ternary output with tuple renaming already normalized. -/
theorem ternaryCases (p : Program 3) (d k raw : OTerm alpha) (psi : Formula alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (out : OTerm beta),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph3 p out (d.relabel j) (k.relabel j) (raw.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases p (Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))) _
  intro beta j Theta out hj hp
  simp only [consTermRename,emptyRename] at hp
  exact step beta j Theta out hj hp

theorem projectionTripleRecover {n : Nat} (p : Program 3) (a b c : Fin n)
    (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (programGraph (.composition p ![.projection a,.projection b,.projection c]) out xs))) :
    Nonempty (Derivation body Delta (graph3 p out (xs a) (xs b) (xs c))) := by
  apply compositionRecover p ![.projection a,.projection b,.projection c] out xs
    (Fin.cons (xs a) (Fin.cons (xs b) (Fin.cons (xs c) Fin.elim0))) h
  intro i
  exact Fin.cases (projectionValue a xs) (Fin.cases (projectionValue b xs)
    (Fin.cases (projectionValue c xs) (fun q => Fin.elim0 q))) i

/-- Both child outputs are selected in one internal existential block. -/
theorem binaryChildCases (p : Program 3) (d k first second : OTerm alpha) (psi : Formula alpha)
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (firstOut secondOut : OTerm beta),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph3 p firstOut (d.relabel j) (k.relabel j) (first.relabel j))) →
      Nonempty (Derivation body Theta (graph3 p secondOut (d.relabel j) (k.relabel j) (second.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let qs : Fin 2 → Program 4 := ![
    (.composition p ![.projection 0,.projection 1,.projection 2]),
    (.composition p ![.projection 0,.projection 1,.projection 3])]
  let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons first (Fin.cons second Fin.elim0)))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  exact step beta j Theta (ys 0) (ys 1) hj
    (projectionTripleRecover p 0 1 2 (ys 0) (fun i => (xs i).relabel j) (hq 0))
    (projectionTripleRecover p 0 1 3 (ys 1) (fun i => (xs i).relabel j) (hq 1))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
