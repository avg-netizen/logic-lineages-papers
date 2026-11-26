module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalLeafParametersProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The frozen shift leaf never reads its erased-type input. This proof
follows its actual composition AST, with all branch tests retained. -/
theorem shiftLeafSubstitution (q : Program 3) :
    Substitutes ![q,Program.projection 1,.projection 2] (leaf .shift) (leaf .shift) := by
  let gs : Fin 3 → Program 3 := ![q,.projection 1,.projection 2]
  have hr : Substitutes gs (.projection 2) (.projection 2) := .projection 2
  have hk : Substitutes gs (.projection 1) (.projection 1) := .projection 1
  have hi := unarySubstitution InternalUnpair.right hr
  exact branchSubstitution (sameSubstitution (unarySubstitution InternalUnpair.left hr)
      (constantSubstitution gs 0)) hr
    (pairSubstitution (constantSubstitution gs 0)
      (branchSubstitution (binarySubstitution InternalLessThan.ltTest hi hk)
        (unarySubstitution .succ hi) hi))

/-- Rank's frozen leaf reads neither erased type nor cutoff. -/
theorem rankLeafSubstitution (q r : Program 3) :
    Substitutes ![q,r,Program.projection 2] (leaf .rank) (leaf .rank) := by
  let gs : Fin 3 → Program 3 := ![q,r,.projection 2]
  have hr : Substitutes gs (.projection 2) (.projection 2) := .projection 2
  exact branchSubstitution (sameSubstitution (unarySubstitution InternalUnpair.left hr)
    (constantSubstitution gs 0)) (constantSubstitution gs 0) (constantSubstitution gs 1)

theorem shiftLeafZero (out d k raw : OTerm alpha) :
    Nonempty (Derivation body Delta (graph3 (leaf .shift) out (numeral 0) k raw)) ↔
      Nonempty (Derivation body Delta (graph3 (leaf .shift) out d k raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  apply substitutionGraph (shiftLeafSubstitution (constant 3 0))
    (Fin.cons (numeral 0) (Fin.cons k (Fin.cons raw Fin.elim0))) xs out
  intro i
  exact Fin.cases (constantValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs) (fun q => Fin.elim0 q))) i

theorem rankLeafZero (out d k raw : OTerm alpha) :
    Nonempty (Derivation body Delta (graph3 (leaf .rank) out (numeral 0) (numeral 0) raw)) ↔
      Nonempty (Derivation body Delta (graph3 (leaf .rank) out d k raw)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons k (Fin.cons raw Fin.elim0))
  apply substitutionGraph (rankLeafSubstitution (constant 3 0) (constant 3 0))
    (Fin.cons (numeral 0) (Fin.cons (numeral 0) (Fin.cons raw Fin.elim0))) xs out
  intro i
  exact Fin.cases (constantValue 0 xs) (Fin.cases (constantValue 0 xs)
    (Fin.cases (projectionValue 2 xs) (fun q => Fin.elim0 q))) i

/-- Parameter independence for every raw natural, not only variable leaves. -/
theorem shiftLeafParameters (out d other k raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (leaf .shift) out d k raw))) :
    Nonempty (Derivation body Delta (graph3 (leaf .shift) out other k raw)) :=
  (shiftLeafZero out other k raw).mp ((shiftLeafZero out d k raw).mpr h)

theorem rankLeafParameters (out d k other otherK raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (leaf .rank) out d k raw))) :
    Nonempty (Derivation body Delta (graph3 (leaf .rank) out other otherK raw)) :=
  (rankLeafZero out other otherK raw).mp ((rankLeafZero out d k raw).mpr h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalLeafParametersProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalLeafParametersProof
