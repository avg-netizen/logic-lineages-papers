import LogicLineages.PersistentMarking.NumberedWindowClassApplicationPath
import LogicLineages.PersistentMarking.NumberedWindowClassApplicationHopTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCheckBits

namespace LogicLineages.PersistentMarking.NumberedWindowClassApplicationPathTargets
open Spine NumberedWindowSyntax NumberedWindowSimulationData
open NumberedWindowClassApplicationPath NumberedWindowClassPathWitnessBits
open NumberedWindowArithmeticPathCode NumberedWindowArithmeticPathCheckBits
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticLeastClass NumberedWindowPathWitnessTargets
open NumberedWindowArithmeticScalarTargets NumberedWindowScalarAlgorithm NumberedWindowExternalApplication

/-- Compare literal witness payloads. The new target class code is
checked by the accepted path, so distinct representatives can rejoin. -/
def LiftedHop (σ τ : Ty) (U : NTerm) (old new : ClassHop) : Prop :=
  new.edge = ⟨.auxApp σ τ old.edge.source U,.auxApp σ τ old.edge.target U,
    .auxFunction old.edge.witness⟩

def ExactPositiveClassPathLift : Prop :=
  ∀ (S : Signature) (K Γ : List Ty) (σ τ : Ty) (hk : DecisionSourceUniverse.Closed K)
    (q r : Class S K (finiteC Γ) (.arrow σ τ)) (u : Class S K (finiteC Γ) σ)
    (i j a imageSource certificate : Nat),
    ActualCodeAt S K Γ (.arrow σ τ) i q →
    ActualCodeAt S K Γ (.arrow σ τ) j r →
    ActualCodeAt S K Γ σ a u →
    ActualCodeAt S K Γ τ imageSource (appClass hk q u) →
    positiveClassPathCodeBit S K Γ (.arrow σ τ) i certificate j = true →
      ∃ (imageTarget output : Nat) (U : NTerm) (oldPath newPath : List ClassHop),
        decodeTerm a = some U ∧
        decodeClassPath certificate = some oldPath ∧
        decodeClassPath output = some newPath ∧
        List.Forall₂ (LiftedHop σ τ U) oldPath newPath ∧
        liftPath (least (fixed S K) (Γ.map encodeTy) (encodeTy τ))
          (encodeTy σ) (encodeTy τ) a imageSource certificate = some (imageTarget,output) ∧
        positiveClassPathCodeBit S K Γ τ imageSource output imageTarget = true ∧
        ActualCodeAt S K Γ τ imageTarget (appClass hk r u)

end LogicLineages.PersistentMarking.NumberedWindowClassApplicationPathTargets
