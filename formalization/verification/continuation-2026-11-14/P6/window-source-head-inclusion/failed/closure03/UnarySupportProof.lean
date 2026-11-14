module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.ClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.SimpleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.UnarySupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open HeadWindowBranchAdequacy (member)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open ClosureProof ClosureSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem chain (a b c : Program 1) (payload out types : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (ArrowClosed types)))
    (hr : Nonempty (Derivation body Delta (graph1
      (OriginalHeadResult.arrow a (OriginalHeadResult.arrow b (OriginalHeadResult.arrow c (.projection 0)))) out payload)))
    (hm : Nonempty (Derivation body Delta (member types out))) :
    Nonempty (Derivation body Delta (member types payload)) := by
  let q := OriginalHeadResult.arrow b (OriginalHeadResult.arrow c (.projection 0))
  apply programCases q (Fin.cons payload Fin.elim0) _
  intro beta j Theta middle hj hq
  simp only [consTermRename,emptyRename] at hq
  have hcj := renameInto hc j Theta hj
  rw [closureRename] at hcj
  have hrj := renameInto hr j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [graph1Rename,member,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hrj hmj ⊢
  have hmid := arrowRight a q (payload.relabel j) (out.relabel j) middle (types.relabel j) hcj hrj hq hmj
  apply programCases (OriginalHeadResult.arrow c (.projection 0)) (Fin.cons (payload.relabel j) Fin.elim0) _
  intro gamma k Xi last hk hl
  simp only [consTermRename,emptyRename] at hl
  have hck := renameInto hcj k Xi hk
  rw [closureRename] at hck
  have hqk := renameInto hq k Xi hk
  have hmk := renameInto hmid k Xi hk
  simp only [graph1Rename,member,graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hqk hmk ⊢
  have hlast := arrowRight b (OriginalHeadResult.arrow c (.projection 0))
    ((payload.relabel j).relabel k) (middle.relabel k) last ((types.relabel j).relabel k) hck hqk hl hmk
  exact arrowRight c (.projection 0) ((payload.relabel j).relabel k) last
    ((payload.relabel j).relabel k) ((types.relabel j).relabel k) hck hl
    (projectionValue 0 (Fin.cons ((payload.relabel j).relabel k) Fin.elim0)) hlast

theorem unaryPayload (which : Fin 2) (raw payload symbols types : OTerm alpha)
    (n : Nat) (arity : Fin n → Nat)
    (hc : Nonempty (Derivation body Delta (ArrowClosed types)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw
      (numeral (RawHeadWindowCoverage.unaryTag which)) payload)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) raw symbols types))) :
    Nonempty (Derivation body Delta (member types payload)) := by
  apply programCases (OriginalHeadResult.branchResult (RawHeadWindowCoverage.unaryTag which)) (Fin.cons payload Fin.elim0) _
  intro beta j Theta result hj hr
  simp only [consTermRename,emptyRename] at hr
  have hcj := renameInto hc j Theta hj
  rw [closureRename] at hcj
  have hpj := renameInto hp j Theta hj
  have hwj := renameInto hw j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hpj hwj
  simp only [member,graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have ht : RawHeadWindowCoverage.unaryTag which < 4 := by
    unfold RawHeadWindowCoverage.unaryTag
    omega
  have hm := (HeadWindowBranchAdequacy.SimpleProof.simple n arity body beta Theta
    ⟨RawHeadWindowCoverage.unaryTag which,ht⟩ (raw.relabel j) (payload.relabel j) result
    (symbols.relabel j) (types.relabel j) hpj hr).mp hwj
  have hi : which.val = 0 ∨ which.val = 1 := by omega
  rcases hi with hi | hi
  · simp only [RawHeadWindowCoverage.unaryTag,hi,Nat.reduceAdd,OriginalHeadResult.branchResult] at hr
    exact chain (OriginalRawSyntaxTransport.constant 1 0) (.projection 0) (.projection 0)
      (payload.relabel j) result (types.relabel j) hcj hr hm
  · simp only [RawHeadWindowCoverage.unaryTag,hi,Nat.reduceAdd,OriginalHeadResult.branchResult] at hr
    exact chain (OriginalRawSyntaxTransport.constant 1 0)
      (OriginalHeadResult.arrow (OriginalRawSyntaxTransport.constant 1 0)
        (OriginalHeadResult.arrow (.projection 0) (.projection 0))) (.projection 0)
      (payload.relabel j) result (types.relabel j) hcj hr hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.UnarySupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.WindowSourceHeadInclusion.UnarySupportProof
