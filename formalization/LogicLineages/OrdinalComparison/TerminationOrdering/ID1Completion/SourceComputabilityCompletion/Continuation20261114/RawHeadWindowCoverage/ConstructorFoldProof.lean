module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.FoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.ConstructorFoldProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open SupportProof FoldCoreProof

def tagTransform (tag : Nat) : Program 1 := pairOf (constant 1 tag) (.projection 0)
theorem tagValue {m : Nat} (tag : Nat) (index : Fin m) (image head : OTerm alpha) (xs : Fin m → OTerm alpha)
    (hx : xs index = head)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing image (numeral tag) head))) :
    Nonempty (Derivation body Delta (programGraph (pairOf (constant m tag) (.projection index)) image xs)) := by
  apply binaryValue InternalPairing.pairing (constant m tag) (.projection index) image (numeral tag) head xs hp
    (constantValue tag xs)
  simpa only [hx] using (projectionValue (body := body) (Gamma := Delta) index xs)
theorem tagRecover (tag : Nat) (image head : OTerm alpha)
    (h : Nonempty (Derivation body Delta (programGraph (tagTransform tag) image (Fin.cons head Fin.elim0)))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing image (numeral tag) head)) :=
  binaryRecover InternalPairing.pairing (constant 1 tag) (.projection 0) image (numeral tag) head
    (Fin.cons head Fin.elim0) h (constantValue tag _) (projectionValue 0 (Fin.cons head Fin.elim0))

theorem doubleTail {m : Nat} (p q r : Program m) (out tail needle : OTerm alpha) (xs : Fin m → OTerm alpha)
    (hr : Nonempty (Derivation body Delta (programGraph r tail xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) tail needle)))
    (ho : Nonempty (Derivation body Delta (programGraph (consOf p (consOf q r)) out xs))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) := by
  apply programCases (consOf q r) xs _
  intro beta j Theta middle hj hmid
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hrj := renameInto hr j Theta hj
  have hoj := renameInto ho j Theta hj
  have hmj := renameInto hm j Theta hj
  simp only [programRename] at hrj hoj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact consTail p (consOf q r) (out.relabel j) middle (needle.relabel j) (fun i => (xs i).relabel j)
    hmid (consTail q r middle (tail.relabel j) (needle.relabel j) _ hrj hmj hmid) hoj

theorem rankedHit : Hit body OriginalSourceHeads.rankedStep (tagTransform 5) := by
  intro alpha Delta head rest out image params ht hs
  have hparams : params = (Fin.elim0 : Fin 0 → OTerm alpha) := by
    funext i
    exact Fin.elim0 i
  rw [hparams] at ht
  have hp := tagRecover 5 image head ht
  exact consHead _ (.projection 1) out image (Fin.cons head (Fin.cons rest params))
    (tagValue 5 0 image head _ rfl hp) hs

theorem rankedTail : Tail body OriginalSourceHeads.rankedStep := by
  intro alpha Delta head rest out image params hm hs
  exact consTail _ (.projection 1) out rest image (Fin.cons head (Fin.cons rest params))
    (projectionValue 1 (Fin.cons head (Fin.cons rest params))) hm hs

theorem rankedCoverage (symbols out image symbol : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 OriginalSourceHeads.rankedHeads out symbols)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing image (numeral 5) symbol)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) symbols symbol))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out image)) :=
  FoldProof.coverage (constant 0 0) OriginalSourceHeads.rankedStep (tagTransform 5) rankedHit rankedTail
    symbols symbol image out Fin.elim0 (tagValue 5 0 image symbol (Fin.cons symbol Fin.elim0) rfl hp) hm hf

theorem unaryHit (which : Fin 2) : Hit body OriginalSourceHeads.caseStep (tagTransform (unaryTag which)) := by
  intro alpha Delta head rest out image params ht hs
  have hparams : params = (Fin.elim0 : Fin 0 → OTerm alpha) := by
    funext i
    exact Fin.elim0 i
  rw [hparams] at ht
  have hp := tagRecover (unaryTag which) image head ht
  revert hp
  refine Fin.cases ?_ (fun i => ?_) which
  · intro hp
    exact consHead _ _ out image (Fin.cons head (Fin.cons rest params)) (tagValue 2 0 image head _ rfl hp) hs
  · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    intro hp
    exact secondHead _ _ _ out image (Fin.cons head (Fin.cons rest params)) (tagValue 3 0 image head _ rfl hp) hs

theorem unaryTail : Tail body OriginalSourceHeads.caseStep := by
  intro alpha Delta head rest out image params hm hs
  exact doubleTail _ _ (.projection 1) out rest image (Fin.cons head (Fin.cons rest params))
    (projectionValue 1 (Fin.cons head (Fin.cons rest params))) hm hs

theorem unaryCoverage (which : Fin 2) (types out image tau : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 OriginalSourceHeads.casesRecursors out types)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing image (numeral (unaryTag which)) tau)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) types tau))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out image)) :=
  FoldProof.coverage (constant 0 0) OriginalSourceHeads.caseStep (tagTransform (unaryTag which)) (unaryHit which) unaryTail
    types tau image out Fin.elim0 (tagValue (unaryTag which) 0 image tau (Fin.cons tau Fin.elim0) rfl hp) hm hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.ConstructorFoldProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.ConstructorFoldProof
