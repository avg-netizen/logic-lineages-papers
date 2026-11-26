module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBranchCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open InternalOriginalPairingOrderArithmeticProof (formulaCases)
open InternalTagArithmeticSyntaxProof (z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Split one actual tag test internally. The accepted branch exposes the
literal numeral graph, and both alternatives retain the original context. -/
theorem numeralBranchCases {n : Nat} (p no yes : Program n)
    (tag : OTerm alpha) (expected : Nat) (out : OTerm alpha)
    (xs : Fin n → OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta (programGraph p tag xs)))
    (ho : Nonempty (Derivation body Delta
      (programGraph (InternalAcceptance.branch (sameOf p (constant n expected)) no yes) out xs)))
    (kn : ∀ Theta : List (Formula alpha), (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta (programGraph no out xs)) →
      Nonempty (Derivation body Theta psi))
    (ky : ∀ Theta : List (Formula alpha), (∀ a ∈ Delta, a ∈ Theta) →
      Nonempty (Derivation body Theta (programGraph p (numeral expected) xs)) →
      Nonempty (Derivation body Theta (programGraph yes out xs)) →
      Nonempty (Derivation body Theta psi)) :
    Nonempty (Derivation body Delta psi) := by
  apply formulaCases (equal tag (numeral expected)) psi
  · let Theta := equal tag (numeral expected) :: Delta
    have inc : ∀ a ∈ Delta, a ∈ Theta := fun a ha => List.mem_cons_of_mem _ ha
    have he : Nonempty (Derivation body Theta (eqn tag (numeral expected))) := by
      simpa only [equalEqn] using (show Nonempty (Derivation body Theta (equal tag (numeral expected))) from
        ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have htag := outputTransport p tag (numeral expected) xs he (weakenProof ht inc)
    exact ky Theta inc htag (successorBranchElim _ no yes out z xs
      (InternalApplicationStepPeelSupportProof.sameAccept p (constant n expected) (numeral expected) xs
        htag (constantValue expected xs)) (weakenProof ho inc))
  · let Theta := (equal tag (numeral expected)).not :: Delta
    have inc : ∀ a ∈ Delta, a ∈ Theta := fun a ha => List.mem_cons_of_mem _ ha
    exact kn Theta inc (zeroBranchElim _ no yes out xs
      (sameReject p (constant n expected) tag (numeral expected) xs
        (weakenProof ht inc) (constantValue expected xs)
        (show Nonempty (Derivation body Theta (equal tag (numeral expected)).not) from
          ⟨Derivation.hypothesis List.mem_cons_self⟩)) (weakenProof ho inc))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBranchCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBranchCasesProof
