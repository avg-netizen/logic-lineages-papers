module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionArityQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalQuotientComparisonProof (orLeft orRight)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorBranchCasesProof
open OriginalRawSyntaxTransportInternalConstructorArityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem arityViewAtQuery {n : Nat} (query : Program n) (raw tag out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag tag raw)))
    (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
    (ha : Nonempty (Derivation body Delta (programGraph (arityOf query) out xs))) :
    Nonempty (Derivation body Delta (ArityView out raw)) := by
  have ht0 := unaryValue InternalUnpair.left query tag raw xs ht hq
  apply numeralBranchCases (leftOf query) _ _ tag 1 out xs (ArityView out raw) ht0 ha
  · intro Theta0 inc0 hn0
    have ht1 := weakenProof ht0 inc0
    apply numeralBranchCases (leftOf query) _ _ tag 4 out xs (ArityView out raw) ht1 hn0
    · intro Theta1 inc1 hn1
      have ht2 := weakenProof ht1 inc1
      apply numeralBranchCases (leftOf query) _ _ tag 2 out xs (ArityView out raw) ht2 hn1
      · intro Theta2 inc2 hn2
        have ht3 := weakenProof ht2 inc2
        apply numeralBranchCases (leftOf query) _ _ tag 5 out xs (ArityView out raw) ht3 hn2
        · intro Theta3 inc3 hn3
          have ht4 := weakenProof ht3 inc3
          apply numeralBranchCases (leftOf query) _ _ tag 7 out xs (ArityView out raw) ht4 hn3
          · intro Theta4 inc4 hn4
            have ht5 := weakenProof ht4 inc4
            obtain ⟨he⟩ := valueUnique (constant n 0) out (numeral 0) xs hn4 (constantValue 0 xs)
            exact ⟨orLeft (by simpa only [equalEqn] using he)⟩
          · intro Theta4 inc4 hv4 hc4
            obtain ⟨he⟩ := valueUnique (constant n 2) out (numeral 2) xs hc4 (constantValue 2 xs)
            obtain ⟨hg⟩ := unaryRecover InternalUnpair.left query (numeral 7) raw xs hv4 (weakenProof hq (fun p hp => inc4 p (inc3 p (inc2 p (inc1 p (inc0 p (hp)))))))
            exact ⟨orRight (orRight (Derivation.conjunctionIntroduction (by simpa only [equalEqn] using he) (orRight (orRight hg))))⟩
        · intro Theta3 inc3 hv3 hc3
          obtain ⟨he⟩ := valueUnique (constant n 2) out (numeral 2) xs hc3 (constantValue 2 xs)
          obtain ⟨hg⟩ := unaryRecover InternalUnpair.left query (numeral 5) raw xs hv3 (weakenProof hq (fun p hp => inc3 p (inc2 p (inc1 p (inc0 p (hp))))))
          exact ⟨orRight (orRight (Derivation.conjunctionIntroduction (by simpa only [equalEqn] using he) (orRight (orLeft hg))))⟩
      · intro Theta2 inc2 hv2 hc2
        obtain ⟨he⟩ := valueUnique (constant n 2) out (numeral 2) xs hc2 (constantValue 2 xs)
        obtain ⟨hg⟩ := unaryRecover InternalUnpair.left query (numeral 2) raw xs hv2 (weakenProof hq (fun p hp => inc2 p (inc1 p (inc0 p (hp)))))
        exact ⟨orRight (orRight (Derivation.conjunctionIntroduction (by simpa only [equalEqn] using he) (orLeft hg)))⟩
    · intro Theta1 inc1 hv1 hc1
      obtain ⟨he⟩ := valueUnique (constant n 1) out (numeral 1) xs hc1 (constantValue 1 xs)
      obtain ⟨hg⟩ := unaryRecover InternalUnpair.left query (numeral 4) raw xs hv1 (weakenProof hq (fun p hp => inc1 p (inc0 p (hp))))
      exact ⟨orRight (orLeft (Derivation.conjunctionIntroduction (by simpa only [equalEqn] using he) (orRight hg)))⟩
  · intro Theta0 inc0 hv0 hc0
    obtain ⟨he⟩ := valueUnique (constant n 1) out (numeral 1) xs hc0 (constantValue 1 xs)
    obtain ⟨hg⟩ := unaryRecover InternalUnpair.left query (numeral 1) raw xs hv0 (weakenProof hq (fun p hp => inc0 p (hp)))
    exact ⟨orRight (orLeft (Derivation.conjunctionIntroduction (by simpa only [equalEqn] using he) (orLeft hg)))⟩


theorem arityViewQuery {n : Nat} (query : Program n) (raw out : OTerm alpha) (xs : Fin n → OTerm alpha)
 (hq : Nonempty (Derivation body Delta (programGraph query raw xs)))
 (ha : Nonempty (Derivation body Delta (programGraph (arityOf query) out xs))) :
 Nonempty (Derivation body Delta (ArityView out raw)) := by
 let rawXs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
 apply programCases rawTag rawXs _
 intro beta rho Theta tag hrho ht
 rw [arityViewRename]
 have hvec : (fun i => (rawXs i).relabel rho) =
   Fin.cons (raw.relabel rho) Fin.elim0 := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hvec] at ht
 have hq' := renameInto hq rho Theta hrho
 have ha' := renameInto ha rho Theta hrho
 simp only [programRename] at hq' ha'
 exact arityViewAtQuery query (raw.relabel rho) tag (out.relabel rho)
   (fun i => (xs i).relabel rho) ht hq' ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionArityQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionArityQueryProof
