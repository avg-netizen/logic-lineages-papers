module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorRankProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Unary rank returns the first child result; it does not count metadata. -/
theorem unaryRankForward (raw first second out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph3 (arityOf (.projection 0)) (numeral 1) raw first second)))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild .rank) out raw first second))) :
    Nonempty (Derivation body Delta (equal out first)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  have h := branchNumeralElim 1 1 (arityOf (.projection 0)) _ _ out xs ha ho
  simpa only [equalEqn] using valueUnique (.projection 1) out first xs h (projectionValue 1 xs)

theorem unaryRankBackward (raw first second out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph3 (arityOf (.projection 0)) (numeral 1) raw first second)))
    (ho : Nonempty (Derivation body Delta (equal out first))) :
    Nonempty (Derivation body Delta (graph3 (rebuild .rank) out raw first second)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  apply branchNumeralIntro 1 1 (arityOf (.projection 0)) _ _ out xs ha
  obtain ⟨he⟩ := ho
  exact outputTransport (.projection 1) first out xs
    ⟨symm (by simpa only [equalEqn] using he)⟩ (projectionValue 1 xs)

/-- Every nonunary rebuild sums the exact two supplied child results. -/
theorem nonunaryRankForward (arity : Nat) (hne : arity ≠ 1) (raw first second out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph3 (arityOf (.projection 0)) (numeral arity) raw first second)))
    (ho : Nonempty (Derivation body Delta (graph3 (rebuild .rank) out raw first second))) :
    Nonempty (Derivation body Delta (graph2 InternalArithmeticPrograms.addition out first second)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  have h := branchNumeralElim arity 1 (arityOf (.projection 0)) _ _ out xs ha ho
  rw [if_neg hne] at h
  exact binaryRecover InternalArithmeticPrograms.addition (.projection 1) (.projection 2)
    out first second xs h (projectionValue 1 xs) (projectionValue 2 xs)

theorem nonunaryRankBackward (arity : Nat) (hne : arity ≠ 1) (raw first second out : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (graph3 (arityOf (.projection 0)) (numeral arity) raw first second)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalArithmeticPrograms.addition out first second))) :
    Nonempty (Derivation body Delta (graph3 (rebuild .rank) out raw first second)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))
  apply branchNumeralIntro arity 1 (arityOf (.projection 0)) _ _ out xs ha
  rw [if_neg hne]
  exact binaryValue InternalArithmeticPrograms.addition (.projection 1) (.projection 2)
    out first second xs ho (projectionValue 1 xs) (projectionValue 2 xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorRankProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorRankProof
