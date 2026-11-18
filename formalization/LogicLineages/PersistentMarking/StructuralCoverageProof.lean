import LogicLineages.PersistentMarking.StructuralCoverageTargets
import LogicLineages.PersistentMarking.StructuralContextProof
import LogicLineages.PersistentMarking.ClosingNamedProof
import LogicLineages.PersistentMarking.BridgeTypingProof
namespace LogicLineages.PersistentMarking.StructuralCoverageProof
open Spine NameBridge StructuralContext StructuralCoverageTargets

mutual
 theorem encodeOrdinary (env : List Name) (q : Term) : NamedOrdinary q ↔ Ordinary (encode env q) := by
  cases q with
  | var σ x => cases hl : nameLookup env (σ,x) <;> simp [encode,hl,NamedOrdinary,Ordinary]
  | lam σ x q => exact encodeOrdinary ((σ,x)::env) q
  | head f qs => exact encodeOrdinaryArgs env qs
  | marked f τ qs es => rfl
 termination_by sizeOf q
 theorem encodeOrdinaryArgs (env : List Name) (qs : List Term) :
    NamedOrdinaryArgs qs ↔ OrdinaryArgs (encodeArgs env qs) := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [NamedOrdinaryArgs,encodeArgs,OrdinaryArgs,encodeOrdinary env q,encodeOrdinaryArgs env qs]
 termination_by sizeOf qs
end

theorem ordinaryEncoding : OrdinaryEncoding := encodeOrdinary

theorem contextCoverage : ContextCoverage := by
  intro S C σ τ hc
  induction hc with
  | hole => exact .hole
  | head hc hf hb hvb hob ha hva hoa hargs ih =>
    exact .head ih hf (BridgeTypingProof.encodeBase [] _ _ hb)
      ((BridgeTypingProof.encodeArgsValidity S [] _).mp hvb) ((encodeOrdinaryArgs [] _).mp hob)
      (BridgeTypingProof.encodeBase [] _ _ ha) ((BridgeTypingProof.encodeArgsValidity S [] _).mp hva)
      ((encodeOrdinaryArgs [] _).mp hoa) hargs
  | bind hc ih => exact .bind ih

theorem namedWeakContext : NamedWeakContext := by
  intro S C σ τ s t hc hs hvs hos ht hvt hot hw
  rw [ClosingNamedProof.namedFill C s,ClosingNamedProof.namedFill C t]
  exact StructuralContextProof.weakContext S _ σ τ _ _ (contextCoverage S C σ τ hc)
    ⟨BridgeTypingProof.encodeTyped [] s σ hs,(BridgeTypingProof.encodeValidity S [] s).mp hvs⟩
    ⟨BridgeTypingProof.encodeTyped [] t σ ht,(BridgeTypingProof.encodeValidity S [] t).mp hvt⟩
    ((encodeOrdinary [] s).mp hos) ((encodeOrdinary [] t).mp hot) hw

theorem namedStrictContext : NamedStrictContext := by
  intro S C σ τ s t hc hs hvs hos ht hvt hot hw
  rw [ClosingNamedProof.namedFill C s,ClosingNamedProof.namedFill C t]
  exact StructuralContextProof.strictContext S _ σ τ _ _ (contextCoverage S C σ τ hc)
    ⟨BridgeTypingProof.encodeTyped [] s σ hs,(BridgeTypingProof.encodeValidity S [] s).mp hvs⟩
    ⟨BridgeTypingProof.encodeTyped [] t σ ht,(BridgeTypingProof.encodeValidity S [] t).mp hvt⟩
    ((encodeOrdinary [] s).mp hos) ((encodeOrdinary [] t).mp hot) hw
end LogicLineages.PersistentMarking.StructuralCoverageProof
