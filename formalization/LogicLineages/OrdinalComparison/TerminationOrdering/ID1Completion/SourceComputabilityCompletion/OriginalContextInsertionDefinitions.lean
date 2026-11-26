module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertion
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The literal original raw-list fold counting each cons. Inputs of the
step are [head, tail length]; neither a type code nor a packed context code
is substituted for the original successor/pair list representation. -/
def lengthStep : Program 2 :=
  .composition .succ (fun _ : Fin 1 => .projection 1)

def length : Program 1 :=
  InternalRawListRecursion.listRec (InternalRawListRecursion.zero : Program 0) lengthStep

def lengthGraph {alpha : Type} (count code : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  programGraph length count (Fin.cons code Fin.elim0)

/-- An ORIGINAL raw front, suffix and inserted suffix. The front length
is the actual cutoff, and the SAME front is appended to both suffixes.
This witness formula enforces position validity, without any type-window
membership or variable-decoder premise. -/
def witnesses {alpha : Type}
    (d cutoff gamma extended front suffix insertedSuffix : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  lengthGraph cutoff front ⊓
    (graph2 InternalApplicationValidityStackAppend.append gamma front suffix ⊓
      (graph2 InternalListCodec.consCode insertedSuffix d suffix ⊓
        graph2 InternalApplicationValidityStackAppend.append extended front insertedSuffix))

/-- Literal insertion into the original encoded context. Its three bound
witnesses are front, suffix, and d::suffix. This is an arithmetic formula,
not a new primitive relation or a native decoding assumption. -/
def Insert {alpha : Type}
    (d cutoff gamma extended : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalFiniteBlocks.block (witnesses (d.relabel Sum.inl) (cutoff.relabel Sum.inl)
    (gamma.relabel Sum.inl) (extended.relabel Sum.inl)
    (.var (.inr (0 : Fin 3))) (.var (.inr 1)) (.var (.inr 2)))

/-- The separate native reading of exactly the four programs in witnesses.
It is used only for calibration, never as an internal derivation premise. -/
def NativeInsert (d cutoff gamma extended : Nat) : Prop :=
  ∃ front suffix insertedSuffix : Nat,
    evaluate length (List.Vector.ofFn ![front]) = cutoff ∧
    evaluate InternalApplicationValidityStackAppend.append
      (List.Vector.ofFn ![front,suffix]) = gamma ∧
    evaluate InternalListCodec.consCode
      (List.Vector.ofFn ![d,suffix]) = insertedSuffix ∧
    evaluate InternalApplicationValidityStackAppend.append
      (List.Vector.ofFn ![front,insertedSuffix]) = extended

/-- The existing arithmetic strict-order formula. -/
def Below {alpha : Type} (index cutoff : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula index cutoff)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertion
