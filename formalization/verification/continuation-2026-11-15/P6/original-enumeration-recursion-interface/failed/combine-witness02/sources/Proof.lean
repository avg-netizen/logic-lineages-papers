module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineBranchesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof (symm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open CombineFrameProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem backward (n : Nat) (x : Frame body Delta) (out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (relation n x out))) :
    Nonempty (Derivation body Delta (graph3 (G n) out x.node x.answers x.param)) := by
  let A := eqn x.f z ⊓ eqn out (numeral 1)
  let B := (eqn x.f z).not ⊓ Targets.positiveOutput n out x.answers x.ts x.hs x.ls x.tb x.vb
  have ha : Nonempty (Derivation body Delta (A.imp (graph3 (G n) out x.node x.answers x.param))) := by
    have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf := outputTransport fuel x.f z ![x.node,x.answers,x.param] (andLeft h) (fuelGraph (x.withHyp A))
    have hv := CombineScalarProof.zeroValue n x.node x.answers x.param hf
    obtain ⟨he⟩ := andRight h
    obtain ⟨hv⟩ := outputTransport (G n) (numeral 1) out ![x.node,x.answers,x.param] ⟨symm he⟩ hv
    exact ⟨Derivation.implicationIntroduction hv⟩
  have hb : Nonempty (Derivation body Delta (B.imp (graph3 (G n) out x.node x.answers x.param))) := by
    have h : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hv⟩ := CombineBranchesProof.nonzeroBackward n (x.withHyp B) out (andLeft h) (andRight h)
    exact ⟨Derivation.implicationIntroduction hv⟩
  obtain ⟨hr⟩ := hr
  obtain ⟨ha⟩ := ha
  obtain ⟨hb⟩ := hb
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hr ha hb⟩

theorem internalCombine : Targets.InternalCombine := by
  intro body alpha Delta n node answers param vb f ts hs ls tb p2 p3 out hn hp h2 h3
  let x : Frame body Delta := {node := node, answers := answers, param := param, vb := vb, f := f,
    ts := ts, hs := hs, ls := ls, tb := tb, p2 := p2, p3 := p3,
    nodePair := hn, parameterPair := hp, secondPair := h2, thirdPair := h3}
  exact ⟨CombineBranchesProof.forward n x out,backward n x out⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.Proof
