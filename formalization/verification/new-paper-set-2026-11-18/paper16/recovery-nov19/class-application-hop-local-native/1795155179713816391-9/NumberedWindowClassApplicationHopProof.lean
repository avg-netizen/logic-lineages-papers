import LogicLineages.PersistentMarking.NumberedWindowClassApplicationHopTargets
import LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticNodeProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof
import LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassCode

namespace LogicLineages.PersistentMarking.NumberedWindowClassApplicationHopProof
open Spine NumberedWindowSyntax NumberedWindowSimulationData
open NumberedWindowClassApplicationHop NumberedWindowClassApplicationHopTargets
open NumberedWindowClassPathWitnessBits NumberedWindowRawWitnessBits
open NumberedWindowRawApplicationLift NumberedWindowRawApplicationLiftChecks
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticLeastClassChecks
open NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticScalarChecks
open NumberedWindowArithmeticPathCode NumberedWindowArithmeticPathCheckBits
open NumberedWindowArithmeticRawWitnessCode NumberedWindowArithmeticRawWitnessCodeChecks
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticFieldAlgorithmChecks
open NumberedWindowArithmeticAllContextBits NumberedWindowTypingBitsChecks
open NumberedWindowPathWitnessTargets NumberedWindowPathWitnessClassCode
open NumberedWindowExternalApplication NumberedWindowPositivePathAlgorithm (edgeView hopView)

private theorem readHop (j : Nat) (e : ClassEdgeWitness) :
    hopView (encodeClassHop ⟨j,e⟩) =
      some (j,encodeTerm e.source,encodeWitness e.witness,encodeTerm e.target) := by
  simp [hopView,edgeView,encodeClassHop,encodeClassEdge,← exact_ExactTaggedNodeCodec.2,
    NumberedWindowArithmeticNodeProof.nodeRound]

private theorem argument {S : Signature} {K Γ : List Ty} {σ : Ty}
    (hk : DecisionSourceUniverse.Closed K) {a : Nat}
    {u : Class S K (finiteC Γ) σ} (hu : ActualCodeAt S K Γ σ a u) :
    ∃ U : WindowCarrier S K (finiteC Γ) σ, decodeTerm a = some U.val ∧ classOf U = u := by
  have valid := (NumberedWindowArithmeticAllContextAdmittedProof.canonical
    S K ⟨Γ,σ,a⟩ hk).mpr ⟨u,hu⟩
  cases h : decodeTerm a with
  | none => simp [canonicalBit,h] at valid
  | some U =>
      simp only [canonicalBit,h,Bool.and_eq_true,decide_eq_true_eq] at valid
      let A : WindowCarrier S K (finiteC Γ) σ :=
        ⟨U,(exact_FiniteWindowBit S K Γ σ U).mp valid.1⟩
      exact ⟨A,rfl,sameClass hk ⟨A,rfl,valid.2⟩ hu⟩

theorem exactHop : ExactClassHopLift := by
  intro S K Γ σ τ hk q r u i j a e hq hr hu he
  obtain ⟨U,hU,classU⟩ := argument hk hu
  have codeU := (exact_TermCodec.1 a U.val).mp hU
  simp only [classEdgeBit,Bool.and_eq_true,decide_eq_true_eq] at he
  have input : windowStepCodeBit S K Γ (.arrow σ τ)
      (encodeTerm e.source) (encodeWitness e.witness) (encodeTerm e.target) = true := by
    simpa only [windowStepCodeBit,between,exact_TermCodec.2.1,exact_RawWitnessCodec.2.1]
      using he.1.1
  have packed := exact_LiftedWindowStep S K Γ σ τ hk u a hu _ _ _ input
  have literal :
      lift (encodeTy σ) (encodeTy τ) a (encodeTerm e.source) (encodeWitness e.witness) (encodeTerm e.target) =
        (encodeTerm (.auxApp σ τ e.source U.val), encodeWitness (.auxFunction e.witness),
          encodeTerm (.auxApp σ τ e.target U.val)) := by
    rw [← codeU]
    exact exact_LiteralLift σ τ U.val e.source e.target e.witness
  let edge : ClassEdgeWitness :=
    ⟨.auxApp σ τ e.source U.val,.auxApp σ τ e.target U.val,.auxFunction e.witness⟩
  have accepted : finiteWindowWitnessBit S K Γ τ edge.witness edge.source edge.target = true := by
    simpa only [literal,windowStepCodeBit,between,exact_TermCodec.2.1,exact_RawWitnessCodec.2.1,edge]
      using packed
  have guards := he.1.1
  simp only [finiteWindowWitnessBit,Bool.and_eq_true] at guards
  let Q : WindowCarrier S K (finiteC Γ) (.arrow σ τ) :=
    ⟨e.source,(exact_FiniteWindowBit S K Γ (.arrow σ τ) e.source).mp guards.1.2⟩
  let R : WindowCarrier S K (finiteC Γ) (.arrow σ τ) :=
    ⟨e.target,(exact_FiniteWindowBit S K Γ (.arrow σ τ) e.target).mp guards.2⟩
  have classQ : classOf Q = q := sameClass hk ⟨Q,rfl,he.1.2⟩ hq
  have classR : classOf R = r := sameClass hk ⟨R,rfl,he.2⟩ hr
  let X := appCarrier hk Q U
  let Y := appCarrier hk R U
  obtain ⟨x,_,hx,_⟩ := exact_LeastCodeSpecification S K Γ τ X.val hk X.property
  obtain ⟨y,_,hy,_⟩ := exact_LeastCodeSpecification S K Γ τ Y.val hk Y.property
  have classX : classOf X = appClass hk q u := by
    rw [← classQ,← classU]
    rfl
  have classY : classOf Y = appClass hk r u := by
    rw [← classR,← classU]
    rfl
  have lx : leastCode S K Γ τ edge.source = some x := hx
  have ly : leastCode S K Γ τ edge.target = some y := hy
  refine ⟨U.val,x,y,hU,?_,?_,⟨X,classX,hx⟩,⟨Y,classY,hy⟩⟩
  · rw [liftHop,readHop]
    simp only [Option.bind_eq_bind,Option.bind_some,literal,exact_LeastRepresentative,
      exact_TermCodec.2.1]
    change (leastCode S K Γ τ edge.source).bind _ = _
    rw [lx]
    simp only [Option.bind_some,ly,encodeClassHop,encodeClassEdge,exact_ExactTaggedNodeCodec.1,edge]
  · simp only [classEdgeBit,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨⟨accepted,lx⟩,ly⟩

end LogicLineages.PersistentMarking.NumberedWindowClassApplicationHopProof
