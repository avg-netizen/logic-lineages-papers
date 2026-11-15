module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
/-- Strengthens the original existential certificate theorem with the explicit
prescribed witness, both effectiveness and actual original numeric checking. -/
def EffectivePrescribedWitness : Prop :=
 ∀ (alpha : Type) [Primcodable alpha] (axCheck : alpha → List Nat → Bool) n
 (f : alpha → Formula n) (sigma : alpha → Fin n → Term 0) (antecedent : alpha → Nat),
 EffectiveNumeral.Family.FormulaEffective f →
 (∀ i, EffectiveNumeral.Family.TermEffective (fun x => sigma x i)) →
 Primrec antecedent →
 (∀ x, GorbowTheoryNumericCertificate.check (axCheck x) 0
  (GorbowSortedSyntaxCode.formulaCode (GorbowStandardInduction.universalClosure (f x))) (antecedent x) = true) →
 Primrec (fun x => produce (f x) (sigma x) (antecedent x)) ∧
 (∀ x, GorbowTheoryNumericCertificate.check (axCheck x) 0
  (GorbowSortedSyntaxCode.formulaCode (GorbowFormulaSubstitution.substituteFormula (sigma x) (f x)))
  (produce (f x) (sigma x) (antecedent x)) = true)
/-- Exact internal equality to the prescribed ORIGINAL numeric trace, not merely
checking an equivalent certificate. All installed ASTs precede f and sigma;
malformed antecedent numbers retain original decode/getD behavior. -/
def InternalPrescribedTrace : Prop :=
 ∀ arity (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old arithmetic x) (mtag : Nat),
 (nodes p)[mtag]? = some ⟨4,SixSol20261113.LiteralRawMP.constructor⟩ →
 ∀ n (f : Formula n) (sigma : Fin n → Term 0) ctx antecedent,
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (certificate mtag I.ctag I.atag I.constructorTag f (numeralInputs (ctx := ctx) sigma) (Term.numeral antecedent))
   (Term.numeral (produce f sigma antecedent))))
/-- Arbitrary runtime coordinates guarded only by actual termValidator0 proofs.
All arity steps preserve one installation, context0, index/fuel and the actual
recursive numeric certificate. No intermediate CORE acceptance is assumed. -/
def InternalRepeatedSpecialization : Prop :=
 ∀ arity (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old arithmetic x) (mtag : Nat),
 (nodes p)[mtag]? = some ⟨4,SixSol20261113.LiteralRawMP.constructor⟩ →
 ∀ n (f : Formula n) ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) n)
 (antecedent index fuel : Term ctx),
 (∀ i, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.vtag (raw.get i)))) →
 let C := Term.numeral (n := ctx) (Encodable.encode
  (GorbowFormulaPrefixCode.encode (GorbowStandardInduction.universalClosure f)))
 let B := value I.ctag I.atag f raw
 let code := certificate mtag I.ctag I.atag I.constructorTag f raw antecedent
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (SixSol20261113.LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add C C) antecedent) (.succ .zero))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.conj (.equal (SixSol20261113.LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add B B) code) (.succ .zero))
   (SixSol20261112.Fuel.success I.verifierTag index fuel .zero (.add B B) code)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.Targets
