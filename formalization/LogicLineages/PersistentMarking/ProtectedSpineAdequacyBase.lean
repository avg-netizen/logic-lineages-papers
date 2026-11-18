import LogicLineages.PersistentMarking.ProtectedSpineAdequacyTargets
import LogicLineages.PersistentMarking.ProtectedSpineFixedApplicationProof
import LogicLineages.PersistentMarking.MarkedConstructorInventoryProof
import LogicLineages.PersistentMarking.MarkedConstructorStabilizationProof

namespace LogicLineages.PersistentMarking.ProtectedSpineAdequacyBase
open Spine NameBridge DecisionInventory DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineFixedApplicationTargets ProtectedSpineAdequacyTargets
open PortNormalization
open MarkedConstructorTargets (PrefixClosed)
open MarkedConstructorOperator (step leastFixedPoint)

def unfoldedValue (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (q : Expr) : Value :=
  valueAt (evaluate S (domain F) F.data.sourceHeads M q) Γ ⟨[],[]⟩

theorem prefixClosed (S : Signature) (F : Inputs S) : PrefixClosed (domain F) :=
  MarkedConstructorInventoryProof.prefixClosed F.source F.target F.sourceType F.targetType
    F.sourcePaper.1 F.targetPaper.1 F.sourceOrdinary F.targetOrdinary

theorem fixed (S : Signature) (F : Inputs S) :
    let M := leastFixedPoint S (domain F) F.data.sourceHeads
    M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads ∧
    step S (domain F) F.data.sourceHeads M = M := by
  have hE := MarkedConstructorEndomapProof.endomap S (domain F) F.data.sourceHeads (prefixClosed S F)
  have hM := MarkedConstructorEndomapProof.monotone S (domain F) F.data.sourceHeads (prefixClosed S F)
  have h := MarkedConstructorStabilizationProof.stabilizes S (domain F) F.data.sourceHeads hE hM
  exact ⟨h.1 _,h.2.2.2.1⟩

theorem sourceCovered (S : Signature) (F : Inputs S) (Γ : Context) (q : Expr)
    (h : Source F Γ q) : Covered (domain F) F.data.sourceHeads q := ⟨h.1,h.2.1⟩

theorem sourcesCovered (S : Signature) (F : Inputs S) (Γ : Context) (qs : Args)
    (h : Sources F Γ qs) : ArgsCovered (domain F) F.data.sourceHeads qs := by
  have hd := (DecisionSourceBasicProof.argsFacts F.data.types F.data.names F.data.sourceHeads Γ qs).mp h
  exact ⟨hd.1,hd.2.1⟩

theorem stageEq (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (q : Expr)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hw : WellFormed F.data.types F.data.ports Γ) (hSource : Source F Γ q)
    (hTyped : Typed EmptyContext q q.type) :
    ValueEq (domain F) q.type Γ (stageValue S F M Γ q) (unfoldedValue S F M Γ q) := by
  have hl := ProtectedSpineInterpretationProof.laws S (domain F) F.data.sourceHeads M (prefixClosed S F) hm
    EmptyContext q q.type hTyped (sourceCovered S F Γ q hSource)
  exact (ProtectedSpineEncodingProof.encodeAt (domain F) q.type _ hl Γ ⟨[],[]⟩
    (ProtectedSpineConcreteInputProof.emptyValid (domain F) Γ hw)).2

theorem rootBits (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (q t : Expr)
    (hm : M ∈ MarkedFamilyCoherence.retained (domain F) F.data.sourceHeads)
    (hw : WellFormed F.data.types F.data.ports Γ) (hSource : Source F Γ q)
    (hTyped : Typed EmptyContext q q.type) (hObs : Observed F Γ t) (ht : q.type = t.type) :
    (stageValue S F M Γ q).weak Γ t = (unfoldedValue S F M Γ q).weak Γ t ∧
    (stageValue S F M Γ q).strict Γ t = (unfoldedValue S F M Γ q).strict Γ t :=
  (stageEq S F M Γ q hm hw hSource hTyped Γ hw (DecisionPortsProof.extensionRefl Γ)).2.1 t (ht.symm ▸ hObs)

end LogicLineages.PersistentMarking.ProtectedSpineAdequacyBase
