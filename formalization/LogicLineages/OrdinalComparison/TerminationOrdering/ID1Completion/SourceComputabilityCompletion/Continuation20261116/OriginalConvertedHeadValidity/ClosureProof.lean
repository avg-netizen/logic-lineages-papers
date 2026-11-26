module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Boolean.PointBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.ClosureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalAcceptanceBranchProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
attribute [local irreducible] programGraph
/-- Helper property, later discharged for every actual converter branch. -/
def ValidOutput (n : Nat) {k : Nat} (p : Program k) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (xs : Fin k → OTerm alpha) (out : OTerm alpha),
    Nonempty (Derivation body Delta (programGraph p out xs)) →
    Nonempty (Derivation body Delta
      (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) out))

theorem branch (n : Nat) {k : Nat} (c a b : Program k)
    (ha : ValidOutput n a) (hb : ValidOutput n b) :
    ValidOutput n (InternalAcceptance.branch c a b) := by
  intro body alpha Delta xs out hw
  apply programCases c xs _
  intro beta j Theta value hj hc
  simp only [graph1Rename,OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof.numeralRelabel]
  have hwj := renameInto hw j Theta hj
  rw [programRename] at hwj
  apply zeroSuccessorCases Theta value _
  · have hz : Nonempty (Derivation body (eqn value z :: Theta) (eqn value z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hcz := outputTransport c value z (fun i => (xs i).relabel j) hz (withHyp hc (eqn value z))
    exact ha body beta _ _ _ (zeroBranchElim c a b (out.relabel j) _ hcz (withHyp hwj (eqn value z)))
  · intro gamma l Xi pred hl he
    simp only [graph1Rename,OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof.numeralRelabel]
    have hcl := renameInto hc l Xi hl
    have hwl := renameInto hwj l Xi hl
    simp only [programRename] at hcl hwl
    have hcs := outputTransport c (value.relabel l) (suc pred)
      (fun i => ((xs i).relabel j).relabel l) he hcl
    exact hb body gamma _ _ _ (successorBranchElim c a b ((out.relabel j).relabel l) pred _ hcs hwl)

theorem unary (n : Nat) (p q : Program 1) (hp : ValidOutput n p) :
    ValidOutput n (.composition p (fun _ : Fin 1 => q)) := by
  intro body alpha Delta xs out hw
  apply programCases q xs _
  intro beta j Theta value hj hq
  simp only [graph1Rename,OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof.numeralRelabel]
  have hwj := renameInto hw j Theta hj
  rw [programRename] at hwj
  exact hp body beta Theta ![value] (out.relabel j)
    (unaryRecover p q (out.relabel j) value (fun i => (xs i).relabel j) hwj hq)

theorem sum (n : Nat) (a b : Program 1) (ha : ValidOutput n a) (hb : ValidOutput n b) :
    ValidOutput n (OriginalEncodedHeadConversion.sumCase a b) :=
  branch n _ _ _ (unary n _ _ ha) (unary n _ _ hb)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.ClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConvertedHeadValidity.ClosureProof
