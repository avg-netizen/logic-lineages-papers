module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootMergeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedRootProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm trans congSuc)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115 OriginalBoundsRecombination OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem labelAt (raw label head typ base types extra payload : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,typ,base,types,extra])))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw))) :
    Nonempty (Derivation body Delta (graph1 (leftOf InternalUnpair.right) label raw)) := by
  have hl := numberedLabel (.projection 0) raw label head typ base types extra ![raw] (projectionValue 0 ![raw]) hc
  have hr := unaryValue InternalUnpair.right (.projection 0) payload raw ![raw] hp (projectionValue 0 ![raw])
  have h := unaryRecover InternalUnpair.left (rightOf (.projection 0)) label payload ![raw] hl hr
  exact unaryValue InternalUnpair.left InternalUnpair.right label payload ![raw] h hp

theorem labelValue (raw label head typ base types extra : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,typ,base,types,extra]))) :
    Nonempty (Derivation body Delta (graph1 (leftOf InternalUnpair.right) label raw)) := by
  apply InternalAcceptanceSupportProof.programCases InternalUnpair.right ![raw] _
  intro beta j Theta payload hj hp
  rw [graph1Rename]
  have hx : (fun i => (![raw] i).relabel j) = (![raw.relabel j] : Fin 1 → OTerm beta) := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  rw [hx] at hp
  have hcj := renameInto hc j Theta hj
  rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hcj
  exact labelAt (raw.relabel j) (label.relabel j) (head.relabel j) (typ.relabel j)
    (base.relabel j) (types.relabel j) (extra.relabel j) payload hcj hp

theorem rootValue (n : Nat) (raw label head typ base types extra rootValue : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,typ,base,types,extra])))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rootValue (suc z) label))) :
    Nonempty (Derivation body Delta (graph1 (root n) rootValue raw)) := by
  have ht := numberedTag (.projection 0) raw label head typ base types extra ![raw] (projectionValue 0 ![raw]) hc
  have ht' := unaryRecover InternalUnpair.left (.projection 0) (numeral 5) raw ![raw] ht (projectionValue 0 ![raw])
  exact RootProof.numberedRoot n raw label rootValue hg ht' (labelValue raw label head typ base types extra hc) hp

theorem mergeValue (rootValue rootLabel child size childLabel label out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rootValue (suc z) rootLabel)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child size childLabel)))
    (hm : Nonempty (Derivation body Delta (graph2 maximum label rootLabel childLabel)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc size) label))) :
    Nonempty (Derivation body Delta (graph2 merge out rootValue child)) := by
  have he : Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn (OrdinaryArithmetic.addTerm (suc z) size) (suc size)) := trans (InternalAdditionLawsProof.leftSuccessor z size) (congSuc (InternalAdditionLawsProof.leftZero size))
  have hp := headTransport InternalPairing.pairing out (suc size) (OrdinaryArithmetic.addTerm (suc z) size)
    (Fin.cons label Fin.elim0) ⟨symm he⟩ ho
  exact MergeProof.mergeValue rootValue child (suc z) rootLabel size childLabel label out hr hc hm hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedRootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedRootProof
