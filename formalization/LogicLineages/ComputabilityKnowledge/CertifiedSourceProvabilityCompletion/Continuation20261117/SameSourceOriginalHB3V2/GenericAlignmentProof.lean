module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.LogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.GenericAlignmentProof
open GorbowSyntax GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel
/-- Pure derivation substitution of a closed equality. The closed term remains
opaque; no source AST or literal-code normalization participates. -/
theorem lift (U : Sentence → Prop) (u : Term 0) (n ctx : Nat)
 (h : Nonempty (Derivation U (.equal u (.add (Term.numeral n) (Term.numeral n))))) :
 Nonempty (Derivation U (.equal (substitute (Fin.elim0 : Fin 0 → Term ctx) u)
  (.add (Term.numeral n) (Term.numeral n)))) := by
 have hh := GorbowDerivationSubstitution.Proof.derivationSubstitution U 0 ctx _ Fin.elim0 h
 change Nonempty (Derivation U (.equal (substitute Fin.elim0 u)
  (.add (substitute Fin.elim0 (Term.numeral n)) (substitute Fin.elim0 (Term.numeral n))))) at hh
 simp only [Logic.substNumeral] at hh
 exact hh
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.GenericAlignmentProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.GenericAlignmentProof
