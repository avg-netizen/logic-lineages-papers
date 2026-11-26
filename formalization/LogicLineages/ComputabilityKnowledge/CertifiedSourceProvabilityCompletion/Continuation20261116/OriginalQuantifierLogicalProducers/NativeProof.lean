module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.NativeSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open HistoryRuleSuffix.NativeProof NativeSupport

theorem singletonAt (isExists : Bool) (args : List.Vector Nat 2) (lineValue : GorbowProofChecker.Line)
 (h : evaluate (lineConstructor isExists) args = Encodable.encode lineValue) :
 evaluate (singletonConstructor isExists) args = GorbowNumericCertificate.certificateNumber [lineValue] := by
 rw [singletonConstructor,twoEval,constantEval,h,NativeSupport.consAt]
 rfl

theorem exactNative : Targets.Native := by
 constructor
 · intro a b
   dsimp only
   have h := lineAt false (.projection 0) (.projection 1)
    (Encodable.encode (GorbowFormulaPrefixCode.encode a) ::ᵥ Encodable.encode (GorbowFormulaPrefixCode.encode b) ::ᵥ nil)
    (GorbowFormulaPrefixCode.encode a) (GorbowFormulaPrefixCode.encode b) rfl rfl
   have hl : evaluate (lineConstructor false)
    (Encodable.encode (GorbowFormulaPrefixCode.encode a) ::ᵥ Encodable.encode (GorbowFormulaPrefixCode.encode b) ::ᵥ nil) =
    Encodable.encode (GorbowProofChecker.logicalLine (.classicalContraposition a b)) := h
   exact ⟨hl,singletonAt false _ _ hl⟩
 · intro a unused
   dsimp only
   obtain ⟨b,hb⟩ := HistoryKernel.CodecTotalProof.listTotal HistoryKernel.CodecTotalProof.natTotal unused
   have hp : evaluate (.projection (1 : Fin 2))
    (Encodable.encode (GorbowFormulaPrefixCode.encode a) ::ᵥ unused ::ᵥ nil) = Encodable.encode b := by
    simpa only [evaluate,show (1 : Fin 2) = (0 : Fin 1).succ from rfl,List.Vector.get_cons_succ,List.Vector.get_cons_zero] using hb.symm
   have h := lineAt true (.projection 0) (.projection 1)
    (Encodable.encode (GorbowFormulaPrefixCode.encode a) ::ᵥ unused ::ᵥ nil)
    (GorbowFormulaPrefixCode.encode a) b rfl hp
   have hl : evaluate (lineConstructor true) (Encodable.encode (GorbowFormulaPrefixCode.encode a) ::ᵥ unused ::ᵥ nil) =
    Encodable.encode (GorbowProofChecker.logicalLine (.existsDualBackward a)) := h
   exact ⟨hl,singletonAt true _ _ hl⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.OriginalQuantifierLogicalProducers.NativeProof
