module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeCoefficientTargets
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeDecoratorTargets
public import LogicLineages.PermittedControl.ActualRawMarkedZeroSuccessorTargets
public import LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessorTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalNode
open MixedSameRankResidue (WeightedOperand)
open ActualCanonicalOperandGrouping (RawTerm encodeTerm groupRaw groupCheckedRaw groupTyped)
open ActualRawSignedStaticCeiling (RawSyntax encodeSyntax)
open ActualRawCanonicalNodeMetadata (classFlagsCode)
open ActualRawCanonicalNodeCoefficient (coefficientCode)
open ActualRawCanonicalNodeDecorator (decorateCode)
open ActualRawMarkedZeroSuccessor (markedSuccessorCode)
open ActualFullLabelPairGuards (Answer)
open ActualFullValueMaximalMetadata (maximalCoefficient)
open ActualCanonicalSymbolicZeroSuccessor (orderedSuccessor canonicalSuccessor)

abbrev GroupedArgs := Int × List RawTerm × List Nat
abbrev Args := Bool × Int × List RawTerm × List Nat
abbrev RawOutcome := Int × Option RawSyntax

def zeroBodyCode (p : GroupedArgs) : Option RawSyntax := do
  let marks ← decorateCode p.2.1 (classFlagsCode p.2.1 p.2.2)
  markedSuccessorCode (p.1,marks)

def groupedCode (p : GroupedArgs) : RawOutcome :=
  let coefficient := coefficientCode p.2.1 p.2.2
  (coefficient,if coefficient = 0 then zeroBodyCode p else none)

/-- The external all-reads-hit report is not checked by this syntax
program. A rejected source (none), accepted nonzero node (some with
its coefficient and no successor), and zero node with failed body
(some with zero coefficient and no successor) are distinct. -/
def nodeCode (p : Args) : Option RawOutcome := do
  let tape ← groupCheckedRaw p.1 p.2.2.1
  pure (groupedCode (p.2.1,tape,p.2.2.2))

def ExactRawNodeBranches : Prop :=
  ∀ (c : Int) (ts : List RawTerm) (answers : List Nat),
    nodeCode (false,c,ts,answers) = none ∧
    nodeCode (true,c,ts,answers) = some (groupedCode (c,groupRaw ts,answers)) ∧
    ∀ v : Int, coefficientCode (groupRaw ts) answers = v → v ≠ 0 →
      nodeCode (true,c,ts,answers) = some (v,none)

def ExactRawOrderedNode : Prop :=
  ∀ (c : Int) (ts : List WeightedOperand) (answers : List Answer),
    groupedCode (c,ts.map encodeTerm,answers.map Answer.code) =
      (maximalCoefficient ts answers,(orderedSuccessor c ts answers).map encodeSyntax)

def ExactRawCanonicalNode : Prop :=
  ∀ (allReadsHit : Bool) (c : Int) (ts : List WeightedOperand) (answers : List Answer),
    nodeCode (allReadsHit,c,ts.map encodeTerm,answers.map Answer.code) =
      if allReadsHit then
        some (maximalCoefficient (groupTyped ts) answers,
          (canonicalSuccessor c ts answers).map encodeSyntax)
      else none

def ExactRawCanonicalNodeEffectivity : Prop :=
  Primrec zeroBodyCode ∧ Primrec groupedCode ∧ Primrec nodeCode

def FullActualRawCanonicalNode : Prop :=
  ExactRawNodeBranches ∧ ExactRawOrderedNode ∧ ExactRawCanonicalNode ∧ ExactRawCanonicalNodeEffectivity

end LogicLineages.PermittedControl.ActualRawCanonicalNode
