module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ChildAnswersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootMergeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ListsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
open Continuation20261115 OriginalCodeBoundsRecursion OriginalBoundsRecombination
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atLists (n : Nat)
    (raw rootLabel head typ left types right lv ls ll rv rs rl childLabel label rootValue collected out rest deps valueRest values : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hel : Nonempty (Derivation body Delta (graph1 (bounds n) lv left)))
    (her : Nonempty (Derivation body Delta (graph1 (bounds n) rv right)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hm : Nonempty (Derivation body Delta (graph2 maximum childLabel ll rl)))
    (hmax : Nonempty (Derivation body Delta (graph2 maximum label rootLabel childLabel)))
    (hroot : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rootValue (suc z) rootLabel)))
    (hcol : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing collected (add ls rs) childLabel)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc (add ls rs)) label)))
    (hdr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest right z)))
    (hds : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps left rest)))
    (hvr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode valueRest rv z)))
    (hvs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values lv valueRest))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) := by
  have ha := ChildAnswersProof.binary n raw left right lv rv rest deps valueRest values
    (OriginalEnumerationDepth.ChildrenProof.numbered raw z rootLabel head typ left types right rest deps hc hdr hds)
    hdr hds hvr hvs hel her
  have hfold := FoldProof.double values valueRest lv rv ls ll rs rl childLabel collected hvr hvs hl hr hm hcol
  have hrootValue := NumberedRootProof.rootValue n raw rootLabel head typ left types right rootValue hc hg hroot
  exact ValueProof.fromValues n raw values rootValue collected out hg ha hrootValue hfold
    (NumberedRootProof.mergeValue rootValue rootLabel collected (add ls rs) childLabel label out hroot hcol hmax ho)

theorem atPairs (n : Nat)
    (raw rootLabel head typ left types right lv ls ll rv rs rl childLabel label rootValue collected out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hel : Nonempty (Derivation body Delta (graph1 (bounds n) lv left)))
    (her : Nonempty (Derivation body Delta (graph1 (bounds n) rv right)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hm : Nonempty (Derivation body Delta (graph2 maximum childLabel ll rl)))
    (hmax : Nonempty (Derivation body Delta (graph2 maximum label rootLabel childLabel)))
    (hroot : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rootValue (suc z) rootLabel)))
    (hcol : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing collected (add ls rs) childLabel)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc (add ls rs)) label)))
    : Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) := by
  apply OriginalEnumerationDepth.ListsProof.binary left right lv rv
  intro beta j Theta rest deps valueRest values hj hdr hds hvr hvs
  rw [graph1Rename]
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have helj := renameInto hel j Theta hj
  have herj := renameInto her j Theta hj
  have hlj := renameInto hl j Theta hj
  have hrj := renameInto hr j Theta hj
  have hmj := renameInto hm j Theta hj
  have hmaxj := renameInto hmax j Theta hj
  have hrootj := renameInto hroot j Theta hj
  have hcolj := renameInto hcol j Theta hj
  have hoj := renameInto ho j Theta hj
  rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hcj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel,addRelabel] at hgj helj herj hlj hrj hmj hmaxj hrootj hcolj hoj
  exact atLists n (raw.relabel j) (rootLabel.relabel j) (head.relabel j) (typ.relabel j) (left.relabel j) (types.relabel j) (right.relabel j) (lv.relabel j) (ls.relabel j) (ll.relabel j) (rv.relabel j) (rs.relabel j) (rl.relabel j) (childLabel.relabel j) (label.relabel j) (rootValue.relabel j) (collected.relabel j) (out.relabel j) rest deps valueRest values
    hcj hgj helj herj hlj hrj hmj hmaxj hrootj hcolj hoj hdr hds hvr hvs

def pairQueries : Fin 2 → Program 3 :=
  ![pairOf (constant 3 1) (.projection 0),pairOf (.projection 1) (.projection 2)]

theorem value (n : Nat)
    (raw rootLabel head typ left types right lv ls ll rv rs rl childLabel label out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![rootLabel,head,typ,left,types,right])))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hel : Nonempty (Derivation body Delta (graph1 (bounds n) lv left)))
    (her : Nonempty (Derivation body Delta (graph1 (bounds n) rv right)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hm : Nonempty (Derivation body Delta (graph2 maximum childLabel ll rl)))
    (hmax : Nonempty (Derivation body Delta (graph2 maximum label rootLabel childLabel)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc (add ls rs)) label)))
    : Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases pairQueries ![rootLabel,add ls rs,childLabel] _
  intro beta j ys Theta hj hq
  rw [graph1Rename]
  have hx : (fun i => (![rootLabel,add ls rs,childLabel] i).relabel j) =
      (![rootLabel.relabel j,add (ls.relabel j) (rs.relabel j),childLabel.relabel j] : Fin 3 → OTerm beta) := by
    funext i
    fin_cases i
    · rfl
    · change (add ls rs).relabel j = add (ls.relabel j) (rs.relabel j)
      exact addRelabel ls rs j
    · rfl
  rw [hx] at hq
  let xs : Fin 3 → OTerm beta := ![rootLabel.relabel j,add (ls.relabel j) (rs.relabel j),childLabel.relabel j]
  have hroot := InternalApplicationCertificateConstructorsSupportProof.binaryRecover InternalPairing.pairing (constant 3 1) (.projection 0)
    (ys 0) (suc z) (rootLabel.relabel j) xs (hq 0)
    (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 xs) (projectionValue 0 xs)
  have hcol := InternalApplicationCertificateConstructorsSupportProof.binaryRecover InternalPairing.pairing (.projection 1) (.projection 2)
    (ys 1) (add (ls.relabel j) (rs.relabel j)) (childLabel.relabel j) xs (hq 1) (projectionValue 1 xs) (projectionValue 2 xs)
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have helj := renameInto hel j Theta hj
  have herj := renameInto her j Theta hj
  have hlj := renameInto hl j Theta hj
  have hrj := renameInto hr j Theta hj
  have hmj := renameInto hm j Theta hj
  have hmaxj := renameInto hmax j Theta hj
  have hoj := renameInto ho j Theta hj
  rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hcj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel,addRelabel] at hgj helj herj hlj hrj hmj hmaxj hoj
  exact atPairs n (raw.relabel j) (rootLabel.relabel j) (head.relabel j) (typ.relabel j) (left.relabel j) (types.relabel j) (right.relabel j) (lv.relabel j) (ls.relabel j) (ll.relabel j) (rv.relabel j) (rs.relabel j) (rl.relabel j) (childLabel.relabel j) (label.relabel j) (ys 0) (ys 1) (out.relabel j)
    hcj hgj helj herj hlj hrj hmj hmaxj hroot hcol hoj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.NumberedValueProof
