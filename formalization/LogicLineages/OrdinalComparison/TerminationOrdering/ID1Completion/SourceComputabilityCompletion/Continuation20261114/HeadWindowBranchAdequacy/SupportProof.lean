module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.StepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.SupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalHeadWindow
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem typeFactor (p : Program 3) (payload symbols types value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph3 p value payload symbols types))) :
    (Nonempty (Derivation body Delta (graph3 (typeMember p) (numeral 1) payload symbols types)) ↔
     Nonempty (Derivation body Delta (member types value))) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons payload (Fin.cons symbols (Fin.cons types Fin.elim0))
  exact ⟨fun h => binaryRecover contains (.projection 2) p (numeral 1) types value xs h (projectionValue 2 xs) hp,
    fun h => binaryValue contains (.projection 2) p (numeral 1) types value xs h (projectionValue 2 xs) hp⟩

theorem resultValue (tag : Nat) (payload symbols types value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.branchResult tag) value payload))) :
    Nonempty (Derivation body Delta (graph3
      (.composition (OriginalHeadResult.branchResult tag) (fun _ : Fin 1 => .projection 0)) value payload symbols types)) :=
  unaryValue (OriginalHeadResult.branchResult tag) (.projection 0) value payload
    (Fin.cons payload (Fin.cons symbols (Fin.cons types Fin.elim0))) hr
    (projectionValue 0 (Fin.cons payload (Fin.cons symbols (Fin.cons types Fin.elim0))))

theorem branchAtValue {m : Nat} (c a b : Program m) (out value : OTerm alpha) (xs : Fin m → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph c value xs)))
    (ha : Nonempty (Derivation body Delta (programGraph a out xs)))
    (hb : Nonempty (Derivation body Delta (programGraph b out xs))) :
    Nonempty (Derivation body Delta (programGraph (InternalAcceptance.branch c a b) out xs)) := by
  apply zeroSuccessorCases Delta value _
  · have hz : Nonempty (Derivation body (eqn value z :: Delta) (eqn value z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact zeroBranchIntro c a b out xs (outputTransport c value z xs hz (withHyp hc (eqn value z)))
      (withHyp ha (eqn value z))
  · intro beta j Theta pred hj he
    simp only [programRename]
    have hcj := renameInto hc j Theta hj
    have hbj := renameInto hb j Theta hj
    simp only [programRename] at hcj hbj
    exact successorBranchIntro c a b (out.relabel j) pred (fun i => (xs i).relabel j)
      (outputTransport c (value.relabel j) (suc pred) _ he hcj) hbj

theorem branchBoth {m : Nat} (c a b : Program m) (out : OTerm alpha) (xs : Fin m → OTerm alpha)
    (ha : Nonempty (Derivation body Delta (programGraph a out xs)))
    (hb : Nonempty (Derivation body Delta (programGraph b out xs))) :
    Nonempty (Derivation body Delta (programGraph (InternalAcceptance.branch c a b) out xs)) := by
  apply programCases c xs _
  intro beta j Theta value hj hc
  simp only [programRename]
  have haj := renameInto ha j Theta hj
  have hbj := renameInto hb j Theta hj
  simp only [programRename] at haj hbj
  exact branchAtValue c a b (out.relabel j) value (fun i => (xs i).relabel j) hc haj hbj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.SupportProof
