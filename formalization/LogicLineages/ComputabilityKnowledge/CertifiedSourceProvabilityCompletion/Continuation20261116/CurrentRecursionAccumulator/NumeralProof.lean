module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.NumeralProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality

theorem exactNumeral : Targets.InternalNumeralTrace := by
 intro installed lhs rhs k t old a baseX pF pR I m base formula step R ctx counter params
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 obtain ⟨hn⟩ := QuotedVerifierMP.QuotationProof.numeralCalculation p R.producerTag
  (producer base formula step) R.h_producer (counter ::ᵥ params) ctx
 rw [NativeProof.raw] at hn
 obtain ⟨hu⟩ := GorbowTheoryProofProof.monotonicity _ U
  (CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX) ctx _ ⟨hn⟩
 simpa only [familyCall,List.Vector.map_cons] using (show Nonempty _ from ⟨hu⟩)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.NumeralProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionAccumulator.NumeralProof
