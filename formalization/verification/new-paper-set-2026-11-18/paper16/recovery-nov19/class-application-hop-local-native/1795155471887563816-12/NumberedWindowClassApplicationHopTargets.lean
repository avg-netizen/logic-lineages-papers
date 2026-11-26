import LogicLineages.PersistentMarking.NumberedWindowClassApplicationHop
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalApplication
import LogicLineages.PersistentMarking.NumberedWindowPathWitnessTargets

namespace LogicLineages.PersistentMarking.NumberedWindowClassApplicationHopTargets
open Spine NumberedWindowSyntax NumberedWindowSimulationData
open NumberedWindowClassApplicationHop NumberedWindowClassPathWitnessBits
open NumberedWindowRawWitnessBits NumberedWindowArithmeticPathCode
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticLeastClass NumberedWindowPathWitnessTargets
open NumberedWindowArithmeticScalarTargets NumberedWindowScalarAlgorithm NumberedWindowExternalApplication

/-- The class identifiers come from the literal lifted edge and agree
with both independently given input classes under actual quotient application. -/
def ExactClassHopLift : Prop :=
  ∀ (S : Signature) (K Γ : List Ty) (σ τ : Ty) (hk : DecisionSourceUniverse.Closed K)
    (q r : Class S K (finiteC Γ) (.arrow σ τ)) (u : Class S K (finiteC Γ) σ)
    (i j a : Nat) (e : ClassEdgeWitness),
    ActualCodeAt S K Γ (.arrow σ τ) i q →
    ActualCodeAt S K Γ (.arrow σ τ) j r →
    ActualCodeAt S K Γ σ a u →
    classEdgeBit S K Γ (.arrow σ τ) i j e = true →
      ∃ (U : NTerm) (x y : Nat),
        decodeTerm a = some U ∧
        let edge : ClassEdgeWitness :=
          ⟨.auxApp σ τ e.source U,.auxApp σ τ e.target U,.auxFunction e.witness⟩
        liftHop (least (fixed S K) (Γ.map encodeTy) (encodeTy τ))
          (encodeTy σ) (encodeTy τ) a (encodeClassHop ⟨j,e⟩) =
          some (x,y,encodeClassHop ⟨y,edge⟩) ∧
        classEdgeBit S K Γ τ x y edge = true ∧
        ActualCodeAt S K Γ τ x (appClass hk q u) ∧
        ActualCodeAt S K Γ τ y (appClass hk r u)

end LogicLineages.PersistentMarking.NumberedWindowClassApplicationHopTargets
