module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryRootProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ChildAnswersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootMergeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.ValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ListsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryValueProof
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
open BinaryRootProof (constructor)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atLists (cons : Bool) (n : Nat)
    (raw typ left right lv ls ll rv rs rl label collected out rest deps valueRest values : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (constructor cons) raw typ left right)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hel : Nonempty (Derivation body Delta (graph1 (bounds n) lv left)))
    (her : Nonempty (Derivation body Delta (graph1 (bounds n) rv right)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hm : Nonempty (Derivation body Delta (graph2 maximum label ll rl)))
    (hcol : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing collected (add ls rs) label)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (if cons then add ls rs else suc (add ls rs)) label)))
    (hdr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest right z)))
    (hds : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps left rest)))
    (hvr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode valueRest rv z)))
    (hvs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode values lv valueRest))) :
    Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) := by
  have ha := ChildAnswersProof.binary n raw left right lv rv rest deps valueRest values
    (OriginalEnumerationDepth.ChildrenProof.binary cons raw z typ left right rest deps hc hdr hds)
    hdr hds hvr hvs hel her
  have hfold := FoldProof.double values valueRest lv rv ls ll rs rl label collected hvr hvs hl hr hm hcol
  have hroot := BinaryRootProof.rootValue cons n raw typ left right hc hg
  cases cons
  · exact ValueProof.fromValues n raw values (suc (suc z)) collected out hg ha hroot hfold
      (RootMergeProof.termRoot (suc (suc z)) collected (add ls rs) label out
        InternalApplicationValidityStackAppendTransitionProof.pairOneZero hcol ho)
  · obtain ⟨he⟩ := valueUnique InternalPairing.pairing collected out ![add ls rs,label] hcol ho
    have hmerge := outputTransport merge collected out ![z,collected] ⟨he⟩ (RootMergeProof.zeroRoot collected (add ls rs) label hcol)
    exact ValueProof.fromValues n raw values z collected out hg ha hroot hfold hmerge

theorem atCollected (cons : Bool) (n : Nat)
    (raw typ left right lv ls ll rv rs rl label collected out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (constructor cons) raw typ left right)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hel : Nonempty (Derivation body Delta (graph1 (bounds n) lv left)))
    (her : Nonempty (Derivation body Delta (graph1 (bounds n) rv right)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hm : Nonempty (Derivation body Delta (graph2 maximum label ll rl)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (if cons then add ls rs else suc (add ls rs)) label)))
    (hcol : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing collected (add ls rs) label)))
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
  have hoj := renameInto ho j Theta hj
  have hcolj := renameInto hcol j Theta hj
  cases cons <;> simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel,addRelabel,Bool.false_eq_true,if_true,if_false] at *
  all_goals exact atLists _ n (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j) (lv.relabel j) (ls.relabel j) (ll.relabel j) (rv.relabel j) (rs.relabel j) (rl.relabel j) (label.relabel j) (collected.relabel j) (out.relabel j) rest deps valueRest values hcj hgj helj herj hlj hrj hmj hcolj hoj hdr hds hvr hvs

theorem value (cons : Bool) (n : Nat)
    (raw typ left right lv ls ll rv rs rl label out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (constructor cons) raw typ left right)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hel : Nonempty (Derivation body Delta (graph1 (bounds n) lv left)))
    (her : Nonempty (Derivation body Delta (graph1 (bounds n) rv right)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing lv ls ll)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rv rs rl)))
    (hm : Nonempty (Derivation body Delta (graph2 maximum label ll rl)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (if cons then add ls rs else suc (add ls rs)) label)))
    : Nonempty (Derivation body Delta (graph1 (bounds n) out raw)) := by
  apply InternalAcceptanceSupportProof.programCases InternalPairing.pairing ![add ls rs,label] _
  intro beta j Theta collected hj hcol
  rw [graph1Rename]
  have hx : (fun i => (![add ls rs,label] i).relabel j) =
      (![add (ls.relabel j) (rs.relabel j),label.relabel j] : Fin 2 → OTerm beta) := by
    funext i
    fin_cases i
    · change (add ls rs).relabel j = add (ls.relabel j) (rs.relabel j)
      exact addRelabel ls rs j
    · rfl
  rw [hx] at hcol
  have hcj := renameInto hc j Theta hj
  have hgj := renameInto hg j Theta hj
  have helj := renameInto hel j Theta hj
  have herj := renameInto her j Theta hj
  have hlj := renameInto hl j Theta hj
  have hrj := renameInto hr j Theta hj
  have hmj := renameInto hm j Theta hj
  have hoj := renameInto ho j Theta hj
  cases cons <;> simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel,addRelabel,Bool.false_eq_true,if_true,if_false] at *
  all_goals exact atCollected _ n (raw.relabel j) (typ.relabel j) (left.relabel j) (right.relabel j) (lv.relabel j) (ls.relabel j) (ll.relabel j) (rv.relabel j) (rs.relabel j) (rl.relabel j) (label.relabel j) collected (out.relabel j) hcj hgj helj herj hlj hrj hmj hoj hcol
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.BinaryValueProof
