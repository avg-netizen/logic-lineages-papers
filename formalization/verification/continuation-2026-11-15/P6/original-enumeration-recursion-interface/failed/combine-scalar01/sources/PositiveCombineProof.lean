module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.PositiveCombineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSupportProof (symm)
open CombineFrameProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem witnesses (n : Nat) (x : Frame body Delta) (k out : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 fuel (suc k) x.node x.answers x.param)))
    (ho : Nonempty (Derivation body Delta (graph3 (G n) out x.node x.answers x.param))) :
    Nonempty (Derivation body Delta (Targets.positiveOutput n out x.answers x.ts x.hs x.ls x.tb x.vb)) := by
  let qs : Fin 3 → Program 3 := ![answer 0,answer 1,positiveLayer n]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs ![x.node,x.answers,x.param] _
  intro beta j ys Theta hj hq
  have hxs : (fun i : Fin 3 => (![x.node,x.answers,x.param] i).relabel j) =
      ![x.node.relabel j,x.answers.relabel j,x.param.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hxs] at hq
  rw [CombineWitnessProof.positiveRename]
  let y := x.rename j Theta hj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
  simp only [graph3Rename,sucRelabel] at hfj hoj
  have ha := CombineScalarProof.answerRecover 0 y.node y.answers y.param (ys 0) (hq 0)
  have hb := CombineScalarProof.answerRecover 1 y.node y.answers y.param (ys 1) (hq 1)
  have hl := CombineScalarProof.layerRecover n y.node y.answers y.param y.vb y.f y.ts y.hs y.ls y.tb y.p2 y.p3
    (ys 0) (ys 1) (ys 2) y.nodePair y.parameterPair y.secondPair y.thirdPair ha hb (hq 2)
  have hv := CombineScalarProof.positiveValue n y.node y.answers y.param (k.relabel j) (ys 2) hfj (hq 2)
  have he := valueUnique (G n) (out.relabel j) (suc (ys 2)) ![y.node,y.answers,y.param] hoj hv
  exact CombineWitnessProof.introduce n (out.relabel j) y.answers y.ts y.hs y.ls y.tb y.vb ys
    (andIntro (andIntro (andIntro ha hb) hl) he)

theorem atFields (n : Nat) (x : Frame body Delta) (k out prior opened value : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 fuel (suc k) x.node x.answers x.param)))
    (hw : Nonempty (Derivation body Delta
      (CombineWitnessProof.fields n out x.answers x.ts x.hs x.ls x.tb x.vb prior opened value))) :
    Nonempty (Derivation body Delta (graph3 (G n) out x.node x.answers x.param)) := by
  have ha := andLeft (andLeft (andLeft hw))
  have hb := andRight (andLeft (andLeft hw))
  have hl := andRight (andLeft hw)
  obtain ⟨he⟩ := andRight hw
  have hp := CombineScalarProof.layerAt n x.node x.answers x.param x.vb x.f x.ts x.hs x.ls x.tb x.p2 x.p3
    prior opened value x.nodePair x.parameterPair x.secondPair x.thirdPair ha hb hl
  have hv := CombineScalarProof.positiveValue n x.node x.answers x.param k value hf hp
  exact outputTransport (G n) (suc value) out ![x.node,x.answers,x.param] ⟨symm he⟩ hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.PositiveCombineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.PositiveCombineProof
