module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.OpenCallEncoding
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.CallRawCopy
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.InnerCode
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FixedFormulaSubstitution PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

theorem specialized {arity ctx : Nat} (p : Program arity) (J : GraphInterface.Tags)
 (ntag : Nat)
 (hc : (nodes p)[J.ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (ha : (nodes p)[J.atag]? = some ⟨2,HistoryAppend.append⟩)
 (hn : (nodes p)[ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩)
 (v : List.Vector (Term ctx) 7) :
 let K : PrescribedRuntimeCallCongruence.Tags := { mtag := 0, ctag := J.ctag, atag := J.atag, constructorTag := 0, rctag := J.ctag, reflexivityTag := 0, numeralTag := ntag }
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (formulaValue J.ctag J.atag
   (GraphInterface.numeral ntag (v.get 3) ::ᵥ GraphInterface.innerInputs ntag v)
   bodyTemplate (UniformRuntimeEnvironmentAgreement.specialize innerEnvironment))
   (equalValue J.ctag J.atag
    (callValue K (v.get 0)
     (GraphInterface.numeral ntag (v.get 1) ::ᵥ GraphInterface.numeral ntag (v.get 2) ::ᵥ
      GraphInterface.numeral ntag .zero ::ᵥ v.get 4 ::ᵥ GraphInterface.numeral ntag (v.get 3) ::ᵥ nil))
    (GraphInterface.numeral ntag (.succ .zero))))) := by
 dsimp only
 let K : PrescribedRuntimeCallCongruence.Tags := { mtag := 0, ctag := J.ctag, atag := J.atag, constructorTag := 0, rctag := J.ctag, reflexivityTag := 0, numeralTag := ntag }
 let e := UniformRuntimeEnvironmentAgreement.specialize innerEnvironment
 let raw := GraphInterface.numeral ntag (v.get 3) ::ᵥ GraphInterface.innerInputs ntag v
 let args : List.Vector (Term 5) 5 := .var 2 ::ᵥ .var 1 ::ᵥ .zero ::ᵥ .var 3 ::ᵥ .var 0 ::ᵥ nil
 have ht : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue J.ctag J.atag e raw (.var 4)) (LiteralNumeralPrefix.numeralCall ntag (v.get 0))) := .logical (.reflexive _)
 obtain ⟨hcall⟩ := OpenCallEncoding.call p K hc ha e raw (.var 4) (v.get 0) args ht
 have nodesK : CurrentRecursionProducerCore.CodecBridge.Nodes p K := ⟨hc,ha,hn⟩
 obtain ⟨hz⟩ := ValueTraceProof.numeral (ctx := ctx) p K hn 0
 obtain ⟨hone⟩ := ValueTraceProof.numeral (ctx := ctx) p K hn 1
 obtain ⟨hargs⟩ := CurrentRecursionProducerCore.CallRawCopy.call p K K nodesK nodesK (v.get 0)
  (args.map (termValue J.ctag J.atag e raw))
  (GraphInterface.numeral ntag (v.get 1) ::ᵥ GraphInterface.numeral ntag (v.get 2) ::ᵥ
   GraphInterface.numeral ntag .zero ::ᵥ v.get 4 ::ᵥ GraphInterface.numeral ntag (v.get 3) ::ᵥ nil)
  (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
    | zero => exact .logical (.reflexive _)
    | succ i => cases i using Fin.cases with
     | zero => exact Support.equalitySymmetry _ _ hz
     | succ i => cases i using Fin.cases with
      | zero => exact .logical (.reflexive _)
      | succ i => cases i using Fin.cases with
       | zero => exact .logical (.reflexive _)
       | succ i => exact Fin.elim0 i)
 obtain ⟨hrhs⟩ := CurrentCompositionCertificate.CallEncodingProof.numeral p J.ctag J.atag hc e raw 1
 have hright := Logic.trans _ _ _ hrhs (Support.equalitySymmetry _ _ hone)
 exact CurrentCompositionCertificate.CodecProof.binary p J.ctag J.atag J.ctag J.atag 0 hc ha hc ha _ _ _ _
  (Logic.trans _ _ _ hcall hargs) hright
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.InnerCode
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.InnerCode
