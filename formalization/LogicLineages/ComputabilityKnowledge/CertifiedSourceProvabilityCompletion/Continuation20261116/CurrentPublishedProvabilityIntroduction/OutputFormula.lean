module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.OuterCode
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.PublishedSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.OutputFormula
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

theorem published {arity ctx : Nat} (p : Program arity) (J : GraphInterface.Tags) (K : PrescribedRuntimeCallCongruence.Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[K.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (pF : Program 1) (c : Code) (sigma : Sentence) (fuel cert proofCode : Term ctx) :
 let v : List.Vector (Term ctx) 7 := Term.numeral (GorbowNamedInternalProvability.checkerTag pF) ::ᵥ
  Term.numeral (Encodable.encode c) ::ᵥ fuel ::ᵥ cert ::ᵥ rawNumeral (PublishedSyntax.argument pF c sigma) ::ᵥ
  Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (rho pF c))) ::ᵥ proofCode ::ᵥ nil
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (impValue J.ctag J.atag (v.get 5) (unaryValue J.ctag 11 (GraphInterface.outerValue J K.numeralTag v)))
   (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma))))))) := by
 dsimp only
 obtain ⟨ho⟩ := OuterCode.encoded p J K hc ha hn (GorbowNamedInternalProvability.checkerTag pF)
  (Encodable.encode c) (PublishedSyntax.argument pF c sigma) fuel cert
  (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (rho pF c)))) proofCode
 obtain ⟨hex⟩ := FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.unary p J.ctag hc 11 _ _ ho
 have hshape : Formula.ex (Formula.ex (SyntaxSupport.checkerBody (GorbowNamedInternalProvability.checkerTag pF)
  (Encodable.encode c) (PublishedSyntax.argument pF c sigma))) = prD pF c sigma :=
  (PublishedSyntax.applyProvShape pF c (PublishedSyntax.argument pF c sigma)).symm
 change Derivation (GorbowPRNumeralCalculation.Theory p) (.equal _
  (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (Formula.ex (Formula.ex
   (SyntaxSupport.checkerBody (GorbowNamedInternalProvability.checkerTag pF) (Encodable.encode c)
    (PublishedSyntax.argument pF c sigma)))))))) at hex
 rw [hshape] at hex
 exact FullFormulaInstantiationValidity.FixedTemplateEncodingSupportProof.binary p J.ctag J.atag hc ha 7 _ _ _ _
  (.logical (.reflexive _)) hex
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.OutputFormula
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.OutputFormula
