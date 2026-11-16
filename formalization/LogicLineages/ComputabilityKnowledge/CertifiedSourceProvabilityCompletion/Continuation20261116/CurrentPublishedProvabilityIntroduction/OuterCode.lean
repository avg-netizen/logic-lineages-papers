module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.FormulaEncoding
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateSyntax
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphInterface
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.ValueTraceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.OuterCode
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

theorem encoded {arity ctx : Nat} (p : Program arity) (J : GraphInterface.Tags) (K : PrescribedRuntimeCallCongruence.Tags)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[K.numeralTag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (tag index : Nat) (u : Term 0) (fuel cert rho proofCode : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (GraphInterface.outerValue J K.numeralTag
   (Term.numeral tag ::ᵥ Term.numeral index ::ᵥ fuel ::ᵥ cert ::ᵥ rawNumeral u ::ᵥ rho ::ᵥ proofCode ::ᵥ nil))
   (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (Formula.ex (SyntaxSupport.checkerBody tag index u))))))) := by
 let v : List.Vector Nat 7 := tag ::ᵥ index ::ᵥ 0 ::ᵥ 0 ::ᵥ 0 ::ᵥ 0 ::ᵥ 0 ::ᵥ nil
 let raw : List.Vector (Term ctx) 3 := LiteralNumeralPrefix.numeralCall K.numeralTag (Term.numeral index) ::ᵥ
  rawNumeral u ::ᵥ LiteralNumeralPrefix.numeralCall K.numeralTag (Term.numeral tag) ::ᵥ nil
 have hv : ∀ i, Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (raw.get i) (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (NativeInputs.outerTerms v u i))))) := by
  intro i
  cases i using Fin.cases with
  | zero => exact Classical.choice (ValueTraceProof.numeral p K hn index)
  | succ i => cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
    | zero => exact Classical.choice (ValueTraceProof.numeral p K hn tag)
    | succ i => exact Fin.elim0 i
 obtain ⟨h⟩ := FormulaEncoding.encoded p J.ctag J.atag hc ha outerEnvironment (.ex bodyTemplate) raw (NativeInputs.outerTerms v u) hv
 rw [TemplateSyntax.outer] at h
 exact ⟨h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.OuterCode
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.OuterCode
