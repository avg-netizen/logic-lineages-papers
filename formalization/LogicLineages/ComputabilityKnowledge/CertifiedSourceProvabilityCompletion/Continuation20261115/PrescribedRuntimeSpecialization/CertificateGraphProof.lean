module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.PrimitiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.CertificateGraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph
theorem singleton {arity ctx : Nat} (p : Program arity) (ctag tag : Nat)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ht : (nodes p)[tag]? = some ⟨2,UniformClosedRule13.lineConstructor⟩)
 (A : Term ctx) (f : Formula 1) (t : Term 0)
 (hA : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal A (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f))))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedRule13Certificate.certificate ctag tag A
   (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode t))))
   (Term.numeral (GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.allInstantiate f t)])))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let a : Term ctx := Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f))
 let b : Term ctx := Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode t))
 have hl := Logic.callCongruence T tag (A ::ᵥ b ::ᵥ nil) (a ::ᵥ b ::ᵥ nil) (fun i => by
  cases i using Fin.cases with
  | zero => exact hA
  | succ i => cases i using Fin.cases with
    | zero => exact .logical (.reflexive b)
    | succ i => exact Fin.elim0 i)
 obtain ⟨hn⟩ := PrimitiveProof.lineNumeral (ctx := ctx) p tag ht f t
 have hline := Logic.trans _ _ _ hl hn
 have hcons := Logic.callCongruence T ctag
  (UniformClosedRule13.lineCall tag A b ::ᵥ (.zero : Term ctx) ::ᵥ nil)
  (Term.numeral (Encodable.encode (GorbowProofChecker.logicalLine (.allInstantiate f t))) ::ᵥ (.zero : Term ctx) ::ᵥ nil)
  (fun i => by
   cases i using Fin.cases with
   | zero => exact hline
   | succ i => cases i using Fin.cases with
     | zero => exact .logical (.reflexive (.zero : Term ctx))
     | succ i => exact Fin.elim0 i)
 obtain ⟨hs⟩ := PrimitiveProof.consNumeral (ctx := ctx) p ctag hc (GorbowProofChecker.logicalLine (.allInstantiate f t))
 exact ⟨Logic.trans _ _ _ hcons hs⟩
theorem mp {arity ctx : Nat} (p : Program arity) (mtag : Nat)
 (hm : (nodes p)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (B implication antecedent : Term ctx) (f : Formula 0) (imp ant : Nat)
 (hb : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal B
  (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)))))
 (hi : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal implication (Term.numeral imp)))
 (ha : Derivation (GorbowPRNumeralCalculation.Theory p) (.equal antecedent (Term.numeral ant))) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralMPRun.certificate mtag .zero B implication antecedent)
   (Term.numeral (GorbowTheoryCertificateOperations.mpCertificate 0 (GorbowSortedSyntaxCode.formulaCode f) imp ant)))) := by
 have h := Logic.callCongruence (GorbowPRNumeralCalculation.Theory p) mtag
  ((.zero : Term ctx) ::ᵥ B ::ᵥ implication ::ᵥ antecedent ::ᵥ nil)
  ((.zero : Term ctx) ::ᵥ Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)) ::ᵥ Term.numeral imp ::ᵥ Term.numeral ant ::ᵥ nil)
  (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive (.zero : Term ctx))
   | succ i => cases i using Fin.cases with
     | zero => exact hb
     | succ i => cases i using Fin.cases with
       | zero => exact hi
       | succ i => cases i using Fin.cases with
         | zero => exact ha
         | succ i => exact Fin.elim0 i)
 obtain ⟨hn⟩ := PrimitiveProof.mpNumeral (ctx := ctx) p mtag hm f imp ant
 exact ⟨Logic.trans _ _ _ h hn⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.CertificateGraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.CertificateGraphProof
