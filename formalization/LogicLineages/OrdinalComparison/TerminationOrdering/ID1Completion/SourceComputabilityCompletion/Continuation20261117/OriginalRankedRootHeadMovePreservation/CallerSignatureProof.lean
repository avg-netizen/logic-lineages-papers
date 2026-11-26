module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.CallerAtSignatureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.HeadIdentityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.CallerSignatureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open OriginalUniverseDecoderTransportSyntaxProof (acceptedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open Continuation20261116.OriginalConcreteHeadSignature

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem ordinary (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right f g base target typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left f base)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right g target)))
    (he : Nonempty (Derivation body Delta (eqn f g)))
    (hbg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (htg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (hp : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) base target)))
    (htag : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (SourceComputabilityFormulaSupportProof.numeral 5) f)))
    (hfg : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (suc z) f)))
    (ha : Nonempty (Derivation body Delta (Accepted (signature n arity) M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Accepted (signature n arity) M W false typ right gamma context)) := by
  apply SignatureCasesProof.cases n arity f _ htag hfg
  intro beta j Theta count args packed hj hargs hH hfields
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  rw [graph2Rename] at hlc' hrc'
  have hbg' := renameInto hbg j Theta hj
  have htg' := renameInto htg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hbg' htg'
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hp'
  have he' := renameInto he j Theta hj
  rw [eqnRelabel] at he'
  have ha' := renameInto ha j Theta hj
  change Nonempty (Derivation body Theta ((Accepted (signature n arity) M W false typ left gamma context).relabel j)) at ha'
  rw [acceptedRename] at ha'
  change Nonempty (Derivation body Theta ((Accepted (signature n arity) M W false typ right gamma context).relabel j))
  rw [acceptedRename]
  exact CallerAtSignatureProof.ordinary n arity M W
    (left.relabel j) (right.relabel j) (f.relabel j) (g.relabel j) (base.relabel j) (target.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) count args packed
    hlc' hrc' he' hbg' htg' hp' hargs hH hfields ha'

theorem numbered (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right label f g recorded base target extraTypes extras typ gamma context : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,f,recorded,base,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,g,recorded,target,extraTypes,extras])))
    (he : Nonempty (Derivation body Delta (eqn f g)))
    (hbg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (htg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (hp : Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (suc z) base target)))
    (htag : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (SourceComputabilityFormulaSupportProof.numeral 5) f)))
    (hfg : Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (suc z) f)))
    (ha : Nonempty (Derivation body Delta (Accepted (signature n arity) M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Accepted (signature n arity) M W false typ right gamma context)) := by
  apply SignatureCasesProof.cases n arity f _ htag hfg
  intro beta j Theta count args packed hj hargs hH hfields
  have hlc' := renameInto hlc j Theta hj
  have hrc' := renameInto hrc j Theta hj
  simp only [programRename,OriginalTypedDecoderTransportBinaryAcceptanceProof.tupleSixRename] at hlc' hrc'
  have hbg' := renameInto hbg j Theta hj
  have htg' := renameInto htg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hbg' htg'
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hp'
  have he' := renameInto he j Theta hj
  rw [eqnRelabel] at he'
  have ha' := renameInto ha j Theta hj
  change Nonempty (Derivation body Theta ((Accepted (signature n arity) M W false typ left gamma context).relabel j)) at ha'
  rw [acceptedRename] at ha'
  change Nonempty (Derivation body Theta ((Accepted (signature n arity) M W false typ right gamma context).relabel j))
  rw [acceptedRename]
  exact CallerAtSignatureProof.numbered n arity M W
    (left.relabel j) (right.relabel j) (label.relabel j) (f.relabel j) (g.relabel j) (recorded.relabel j) (base.relabel j) (target.relabel j) (extraTypes.relabel j) (extras.relabel j) (typ.relabel j) (gamma.relabel j) (context.relabel j) count args packed
    hlc' hrc' he' hbg' htg' hp' hargs hH hfields ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.CallerSignatureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.CallerSignatureProof
