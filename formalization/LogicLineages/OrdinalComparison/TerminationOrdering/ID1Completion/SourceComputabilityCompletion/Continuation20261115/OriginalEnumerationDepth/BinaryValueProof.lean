module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.ListsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinarySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel eqnRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def constructor (cons : Bool) := if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor

theorem value (cons : Bool) (n : Nat) (raw typ left right dl dr maximum : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 (constructor cons) raw typ left right)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hl : Nonempty (Derivation body Delta (graph1 (depth n) dl left)))
    (hr : Nonempty (Derivation body Delta (graph1 (depth n) dr right)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum dl dr))) :
    Nonempty (Derivation body Delta (graph1 (depth n) (suc maximum) raw)) := by
  apply ListsProof.binary left right dl dr
  intro beta j Theta rest deps valueRest values hj hdrest hd hvrest hv
  simp only [graph1Rename,sucRelabel]
  have hcj := renameInto hc j Theta hj
  rw [graph3Rename] at hcj
  have hgj := renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj
  have hlj := renameInto hl j Theta hj
  rw [graph1Rename] at hlj
  have hrj := renameInto hr j Theta hj
  rw [graph1Rename] at hrj
  have hmj := renameInto hm j Theta hj
  rw [graph2Rename] at hmj
  exact ChildValuesProof.binary n (raw.relabel j) (left.relabel j) (right.relabel j)
    (dl.relabel j) (dr.relabel j) (maximum.relabel j) rest deps valueRest values hgj
    (ChildrenProof.binary cons (raw.relabel j) z (typ.relabel j) (left.relabel j) (right.relabel j) rest deps hcj hdrest hd)
    hdrest hd hvrest hv hlj hrj hmj

theorem numberedRename {beta : Type} (raw label head typ base types extra : OTerm alpha) (j : alpha → beta) :
    (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![label,head,typ,base,types,extra]).relabel j =
      programGraph OriginalRawSyntaxTransport.numberedConstructor (raw.relabel j)
        ![label.relabel j,head.relabel j,typ.relabel j,base.relabel j,types.relabel j,extra.relabel j] := by
  have hx : (fun i => (![label,head,typ,base,types,extra] i).relabel j) =
      ![label.relabel j,head.relabel j,typ.relabel j,base.relabel j,types.relabel j,extra.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [programRename,hx]

theorem numbered (n : Nat) (raw label head typ base types extra db de maximum : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor raw ![label,head,typ,base,types,extra])))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hb : Nonempty (Derivation body Delta (graph1 (depth n) db base)))
    (he : Nonempty (Derivation body Delta (graph1 (depth n) de extra)))
    (hm : Nonempty (Derivation body Delta (graph2 OriginalBoundsRecombination.maximum maximum db de))) :
    Nonempty (Derivation body Delta (graph1 (depth n) (suc maximum) raw)) := by
  apply ListsProof.binary base extra db de
  intro beta j Theta rest deps valueRest values hj hdrest hd hvrest hv
  simp only [graph1Rename,sucRelabel]
  have hcj := renameInto hc j Theta hj
  rw [numberedRename] at hcj
  have hgj := renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hgj
  have hbj := renameInto hb j Theta hj
  rw [graph1Rename] at hbj
  have hej := renameInto he j Theta hj
  rw [graph1Rename] at hej
  have hmj := renameInto hm j Theta hj
  rw [graph2Rename] at hmj
  exact ChildValuesProof.binary n (raw.relabel j) (base.relabel j) (extra.relabel j)
    (db.relabel j) (de.relabel j) (maximum.relabel j) rest deps valueRest values hgj
    (ChildrenProof.numbered (raw.relabel j) z (label.relabel j) (head.relabel j) (typ.relabel j) (base.relabel j) (types.relabel j) (extra.relabel j) rest deps hcj hdrest hd)
    hdrest hd hvrest hv hbj hej hmj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryValueProof
