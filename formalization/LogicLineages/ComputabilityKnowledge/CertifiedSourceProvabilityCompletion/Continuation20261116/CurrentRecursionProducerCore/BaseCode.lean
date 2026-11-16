module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.BaseSeed
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.TransitivityCopy
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.FormulaBridge
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.BaseCode
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph

theorem value {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : CurrentRecursionProducerSource.Installation p installed lhs rhs t old a baseX base step B G)
 (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionBaseProgram.value R.BJ (Term.numeral R.qTag) inputs)
   (CurrentRecursionBaseCertificate.certificate I.previous R.qTag inputs
    (call (R.qTag+1) inputs) (childCode R.BTag (R.qTag+1) inputs)))) := by
 let J := tags I.previous
 let C := CurrentCalculationFormulaProgram.codecTags R.BJ.ctag R.BJ.atag R.BJ.ntag
 let K : CurrentRecursionBaseProgram.Tags :=
  { ptag := R.BJ.ptag
    ctag := I.previous.previous.current.ctag
    atag := I.previous.previous.current.atag
    ntag := J.numeralTag
    mtag := J.mtag
    r12 := J.constructorTag
    r13 := I.previous.previous.current.constructorTag
    baseTag := R.BJ.baseTag
    childTag := R.BJ.childTag }
 have hC : CodecBridge.Nodes p C := ⟨R.baseInstallation.hc,R.baseInstallation.ha,R.baseInstallation.hn⟩
 have hJ := FormulaBridge.originalNodes p installed lhs rhs t old a _ I
 have hm := I.previous.previous.previous.previous.previous.hmp
 have hn (i : Fin m) := CodecBridge.numeral p C J hC hJ (inputs.get i)
 obtain ⟨hnums⟩ := SpecializationCopy.finiteWitness m (fun i => Derivation (GorbowPRNumeralCalculation.Theory p)
   (.equal (LiteralNumeralPrefix.numeralCall R.BJ.ntag (inputs.get i))
    (LiteralNumeralPrefix.numeralCall J.numeralTag (inputs.get i)))) hn
 obtain ⟨hseed⟩ := BaseSeed.certificate p R.BJ K R.baseInstallation.hp R.baseInstallation.hc R.baseInstallation.ha
  R.baseInstallation.hm R.baseInstallation.h13 R.baseInstallation.hn
  I.previous.previous.current.h_ctag I.previous.previous.current.h_atag hm I.previous.previous.current.h_constructor
  R.qTag inputs (inputs.map (LiteralNumeralPrefix.numeralCall J.numeralTag)) (fun i => by
   simpa only [List.Vector.get_map] using hnums i)
 obtain ⟨hparent⟩ := CodecBridge.call p C J hC hJ (Term.numeral R.qTag) (.zero ::ᵥ inputs)
 obtain ⟨hchild⟩ := CodecBridge.call p C J hC hJ (Term.numeral (R.qTag+1)) inputs
 obtain ⟨hout⟩ := CodecBridge.numeral p C J hC hJ (call (R.qTag+1) inputs)
 have hcode : Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call R.BJ.childTag (.succ (Term.numeral R.qTag) ::ᵥ inputs)) (childCode R.BTag (R.qTag+1) inputs)) := by
  rw [R.baseChildAddress]
  exact .logical (.reflexive _)
 have h := TransitivityCopy.certificate p R.BJ.mtag R.BJ.ctag R.BJ.atag R.BJ.r12 J.mtag J.ctag J.atag J.constructorTag
  R.baseInstallation.hm R.baseInstallation.hc R.baseInstallation.ha R.baseInstallation.h12
  hm hJ.hc hJ.ha I.previous.current.h_constructor
  _ _ _ _ _ _ _ _ _ _ hparent hchild hout hseed hcode
 simp only [CurrentRecursionBaseProgram.value,CurrentRecursionBaseCertificate.certificate,
  CurrentRecursionBaseCertificate.numeralValues,CurrentCompositionCertificate.numeralValues,
  List.Vector.map_cons,R.baseAddress,C,K,J,CurrentCalculationFormulaProgram.codecTags] at h ⊢
 exact h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.BaseCode
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.BaseCode
