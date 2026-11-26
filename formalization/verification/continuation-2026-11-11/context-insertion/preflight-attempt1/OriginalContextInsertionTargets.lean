module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypeCodecPrimrecDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors Source NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalContextInsertion

/-- The original Encodable Gamma instance, not typesNumber. The native
length and append equations alone do not provide arithmetic derivations. -/
def ActualOriginalContextInsertionListCalibration : Prop :=
  (∀ Gamma : List Ty,
    evaluate length (List.Vector.ofFn ![Encodable.encode Gamma]) = Gamma.length) ∧
  (∀ prefix suffix : List Ty,
    evaluate InternalApplicationValidityStackAppend.append
      (List.Vector.ofFn ![Encodable.encode prefix,Encodable.encode suffix]) =
      Encodable.encode (prefix ++ suffix))

/-- Exact arbitrary-position insertion calibration, including the converse.
The exposed prefix has length cutoff, so insertion beyond Gamma is excluded. -/
def ActualOriginalContextInsertionCalibration : Prop :=
  ∀ (d : Ty) (cutoff : Nat) (Gamma extended : List Ty),
    NativeInsert (typeNumber d) cutoff (Encodable.encode Gamma) (Encodable.encode extended) ↔
      ∃ prefix suffix : List Ty,
        Gamma = prefix ++ suffix ∧ extended = prefix ++ (d :: suffix) ∧ prefix.length = cutoff

/-- Zero insertion is precisely the ORIGINAL cons graph, at arbitrary raw
symbolic type/context codes and with no finite type-window premise. -/
def ActualOriginalContextInsertionZero : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type)
    (d gamma extended : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((Insert d OrdinaryArithmetic.zeroTerm gamma extended).iff
        (graph2 InternalListCodec.consCode extended d gamma)))

/-- Under two ORIGINAL cons graphs with the SAME head, insertion at successor
cutoff is equivalent to insertion into their tails at the predecessor cutoff. -/
def ActualOriginalContextInsertionCons : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type)
    (d cutoff gamma extended head tail extendedTail : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((graph2 InternalListCodec.consCode gamma head tail ⊓
        graph2 InternalListCodec.consCode extended head extendedTail).imp
      ((Insert d (OrdinaryArithmetic.succTerm cutoff) gamma extended).iff
        (Insert d cutoff tail extendedTail))))

/-- Below the valid insertion position, the exact original checker graph is
unchanged, including rejection and arbitrary output values. -/
def ActualOriginalContextInsertionVariableBelow : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type)
    (out typ index d cutoff gamma extended : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((Insert d cutoff gamma extended ⊓ Below index cutoff).imp
        ((OriginalVariableDecoder.graph out typ index gamma).iff
          (OriginalVariableDecoder.graph out typ index extended))))

/-- At the inserted position the original checker is exactly the original
equality test against d. Thus successful erasure at this position forces
the requested type to equal d; no erased-type membership is assumed. -/
def ActualOriginalContextInsertionVariableAt : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type)
    (out typ d cutoff gamma extended : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((Insert d cutoff gamma extended).imp
        ((OriginalVariableDecoder.graph out typ cutoff extended).iff
          (testSpec out typ d))))

/-- At or above cutoff, original variable weakening increments the index
and retains the entire original checker output. Reversing this equivalence
is predecessor transport for an extended index strictly above cutoff. -/
def ActualOriginalContextInsertionVariableAbove : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type)
    (out typ index d cutoff gamma extended : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((Insert d cutoff gamma extended ⊓ (Below index cutoff).not).imp
        ((OriginalVariableDecoder.graph out typ index gamma).iff
          (OriginalVariableDecoder.graph out typ (OrdinaryArithmetic.succTerm index) extended))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionTargets
