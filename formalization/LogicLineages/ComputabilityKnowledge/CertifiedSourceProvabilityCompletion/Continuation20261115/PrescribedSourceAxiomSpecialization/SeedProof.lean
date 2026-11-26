module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.SourceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.SeedProof
open GorbowSyntax GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
theorem doubleCode {ctx : Nat} (T : Sentence → Prop) (G : List (Formula ctx))
 (tag : Nat) (index fuel code : Term ctx) (sigma : Sentence)
 (h : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall tag index fuel .zero
   (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)) code) (.succ .zero))) :
 Nonempty (Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall tag index fuel .zero
   (.add (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode sigma)))
    (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode sigma)))) code) (.succ .zero))) := by
 obtain ⟨hq⟩ := FiniteRuleFourCertificate.EncodingProof.formula (ctx := ctx) T sigma
 have he : Hilbert.Local T ctx G
  (.equal (LiteralCheckerAcceptance.coreCall tag index fuel .zero
   (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)) code)
   (LiteralCheckerAcceptance.coreCall tag index fuel .zero
    (.add (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode sigma)))
     (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode sigma)))) code)) := by
  apply callCongruence (T := T) (G := G) tag
  intro i
  cases i using Fin.cases with
  | zero => exact .base (.logical (.reflexive index))
  | succ i => cases i using Fin.cases with
    | zero => exact .base (.logical (.reflexive fuel))
    | succ i => cases i using Fin.cases with
      | zero => exact .base (.logical (.reflexive (.zero : Term ctx)))
      | succ i => cases i using Fin.cases with
        | zero => exact .base hq
        | succ i => cases i using Fin.cases with
          | zero => exact .base (.logical (.reflexive code))
          | succ i => exact Fin.elim0 i
 exact ⟨localTrans _ _ _ (Hilbert.Local.mp (.base (Logic.symmetryRule T _ _)) he) h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.SeedProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.SeedProof
