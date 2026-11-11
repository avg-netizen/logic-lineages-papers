module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternal
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal variable branch specification, with cutoff comparisons in the
object arithmetic. The erasing equality branch returns bottom of d, not of any
surrounding result type. The last branch uses truncated predecessor only when
its index is strictly above the cutoff. -/
def VariableSpec {alpha : Type} (mode : Mode) (out d k i : OTerm alpha) : Formula alpha :=
  match mode with
  | .rank => equal out (numeral 1)
  | .shift =>
      (InternalLessThan.strictLess i k ⊓ graph1 variableConstructor out i) ⊔
      ((InternalLessThan.strictLess i k).not ⊓
        graph1 variableConstructor out (OrdinaryArithmetic.succTerm i))
  | .erase =>
      (InternalLessThan.strictLess i k ⊓ graph1 variableConstructor out i) ⊔
      ((equal i k ⊓ graph1 bottomConstructor out d) ⊔
        (InternalLessThan.strictLess k i ⊓ existsOne
          (graph1 InternalEqualityTest.predecessor (.var (.inr 0)) (i.relabel Sum.inl) ⊓
            graph1 variableConstructor (out.relabel Sum.inl) (.var (.inr 0)))))

/-- Rank uses the computed child count. Shift/erase retain the literal
constructor and its exact original metadata. -/
def UnaryResult {alpha : Type} (mode : Mode) (constructor : Program 2)
    (out metadata child : OTerm alpha) : Formula alpha :=
  match mode with
  | .rank => equal out child
  | .shift | .erase => graph2 constructor out metadata child

def BinaryResult {alpha : Type} (mode : Mode) (constructor : Program 3)
    (out metadata first second : OTerm alpha) : Formula alpha :=
  match mode with
  | .rank => graph2 InternalArithmeticPrograms.addition out first second
  | .shift | .erase => graph3 constructor out metadata first second

def NumberedResult {alpha : Type} (mode : Mode)
    (out label head tau base types extras : OTerm alpha) : Formula alpha :=
  match mode with
  | .rank => graph2 InternalArithmeticPrograms.addition out base extras
  | .shift | .erase => programGraph numberedConstructor out ![label,head,tau,base,types,extras]

def UnchangedLeafResult {alpha : Type} (mode : Mode) (out raw : OTerm alpha) : Formula alpha :=
  match mode with
  | .rank => equal out (numeral 0)
  | .shift | .erase => equal out raw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternal
