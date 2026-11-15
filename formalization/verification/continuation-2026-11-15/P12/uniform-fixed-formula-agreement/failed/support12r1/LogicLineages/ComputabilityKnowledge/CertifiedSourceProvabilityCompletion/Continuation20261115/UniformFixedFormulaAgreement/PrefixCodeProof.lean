module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.SegmentProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.PrefixCodeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph
/-- The finite literal traversal input is the original Nat-list codec, proved
by installed cons equations rather than any syntax-validity reflection. -/
theorem encoded {n ctx : Nat} (p : Program n) (ctag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (xs : List Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (SegmentProof.tokenPrefix ctag xs (.zero : Term ctx))
   (Term.numeral (Encodable.encode xs)))) := by
 induction xs with
 | nil => exact ⟨.logical (.reflexive .zero)⟩
 | cons a xs ih =>
  obtain ⟨hi⟩ := ih
  have hcong := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) ctag
   (Term.numeral a ::ᵥ SegmentProof.tokenPrefix ctag xs (.zero : Term ctx) ::ᵥ nil)
   (Term.numeral a ::ᵥ Term.numeral (Encodable.encode xs) ::ᵥ nil) (fun i => by
    cases i using Fin.cases with
    | zero => exact .logical (.reflexive _)
    | succ i => cases i using Fin.cases with
      | zero => exact hi
      | succ i => exact Fin.elim0 i)
  obtain ⟨hn⟩ := FullFormulaInstantiationValidity.BoundVariableArithmeticProof.numeralCons p ctag hc a xs
  exact ⟨Logic.trans _ _ _ hcong hn⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.PrefixCodeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.PrefixCodeProof
