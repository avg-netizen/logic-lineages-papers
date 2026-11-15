module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineScalarProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineFrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
variable {alpha : Type}
attribute [local irreducible] programGraph

structure Frame (body : Positive (Fin 1)) (Delta : List (Formula alpha)) where
  node : OTerm alpha
  answers : OTerm alpha
  param : OTerm alpha
  vb : OTerm alpha
  f : OTerm alpha
  ts : OTerm alpha
  hs : OTerm alpha
  ls : OTerm alpha
  tb : OTerm alpha
  p2 : OTerm alpha
  p3 : OTerm alpha
  nodePair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb f))
  parameterPair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2))
  secondPair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3))
  thirdPair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb))

variable {body : Positive (Fin 1)} {Delta : List (Formula alpha)}

def Frame.rename {beta : Type} (x : Frame body Delta) (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ p ∈ Delta, p.relabel j ∈ Theta) : Frame body Theta where
  node := x.node.relabel j
  answers := x.answers.relabel j
  param := x.param.relabel j
  vb := x.vb.relabel j
  f := x.f.relabel j
  ts := x.ts.relabel j
  hs := x.hs.relabel j
  ls := x.ls.relabel j
  tb := x.tb.relabel j
  p2 := x.p2.relabel j
  p3 := x.p3.relabel j
  nodePair := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto x.nodePair j Theta hj
    simpa only [graph2Rename] using h
  parameterPair := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto x.parameterPair j Theta hj
    simpa only [graph2Rename] using h
  secondPair := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto x.secondPair j Theta hj
    simpa only [graph2Rename] using h
  thirdPair := by
    have h := InternalGraphCompositionFunctionalityProof.renameInto x.thirdPair j Theta hj
    simpa only [graph2Rename] using h

def Frame.withHyp (x : Frame body Delta) (p : Formula alpha) : Frame body (p :: Delta) where
  node := x.node
  answers := x.answers
  param := x.param
  vb := x.vb
  f := x.f
  ts := x.ts
  hs := x.hs
  ls := x.ls
  tb := x.tb
  p2 := x.p2
  p3 := x.p3
  nodePair := InternalApplicationValidityStackAppendInductionCoreProof.withHyp x.nodePair p
  parameterPair := InternalApplicationValidityStackAppendInductionCoreProof.withHyp x.parameterPair p
  secondPair := InternalApplicationValidityStackAppendInductionCoreProof.withHyp x.secondPair p
  thirdPair := InternalApplicationValidityStackAppendInductionCoreProof.withHyp x.thirdPair p

def relation (n : Nat) (x : Frame body Delta) (out : OTerm alpha) : Formula alpha :=
  (eqn x.f z ⊓ eqn out (numeral 1)) ⊔
    ((eqn x.f z).not ⊓ Targets.positiveOutput n out x.answers x.ts x.hs x.ls x.tb x.vb)

theorem relationRename {beta : Type} (n : Nat) (x : Frame body Delta) (out : OTerm alpha)
    (j : alpha → beta) (Theta : List (Formula beta)) (hj : ∀ p ∈ Delta, p.relabel j ∈ Theta) :
    (relation n x out).relabel j = relation n (x.rename j Theta hj) (out.relabel j) := by
  simp only [relation,OriginalCodeValidityConstructors.Proof.disjRename,
    InternalRecursionGraphStepSyntaxProof.conjunctionRename,CombineWitnessProof.positiveRename,
    eqnRelabel,zRelabel,OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof.numeralRelabel,
    OriginalTypedDecoderTransportLogicalProof.notRename,Frame.rename]

theorem fuelGraph (x : Frame body Delta) :
    Nonempty (Derivation body Delta (graph3 fuel x.f x.node x.answers x.param)) :=
  SelectorProof.fuelAt x.node x.answers x.param x.vb x.f x.nodePair
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineFrameProof
