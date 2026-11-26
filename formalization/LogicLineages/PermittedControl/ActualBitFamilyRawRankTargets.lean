module
public import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutTargets
public import LogicLineages.PermittedControl.ActualBitFamilyHighTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawRank
open FieldComparison (LongFieldCode)
open PreparedProjection (LowerOperandCode)
open MixedSameRankResidue (WeightedCode)
open HeterogeneousSignedMatrixSlice (RawRow TestCode)
open ActualFiniteOrderBranches (Pattern rename)
open ActualBitFamilyRawLayout (RawBitRow RawFamily encodeFamily occurrences)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyHigh (ranked)

def rankCode (p : Pattern × Nat) : Nat := rename p.1 p.2

def operandCode (p : Pattern) (op : LowerOperandCode) : LowerOperandCode :=
  (op.1,rankCode (p,op.2.1),op.2.2)

def termCode (p : Pattern) (t : WeightedCode) : WeightedCode :=
  (t.1,operandCode p t.2)

def rowCode (p : Pattern) (r : RawRow) : RawRow :=
  (r.1,r.2.1,r.2.2.map (termCode p))

def bitCode (p : Pattern) (r : RawBitRow) : RawBitRow := (rowCode p r.1,r.2)

def familyCode (p : Pattern × RawFamily) : RawFamily := p.2.map (List.map (bitCode p.1))

/-- Full payload with only the affected coordinate erased. This keeps
the test, finite modulus, constant, signed coefficient, operand tag,
ordinal/iterate payload and intended bit in their own literal order. -/
def metadata (r : RawBitRow) : TestCode × Int × List (Int × Nat × LongFieldCode) × Bool :=
  (r.1.1,r.1.2.1,r.1.2.2.map (fun t => (t.1,t.2.1,t.2.2.2)),r.2)

def ExactRawRankCalibration : Prop :=
  ∀ (p : Pattern) (family : Family),
    familyCode (p,encodeFamily family) = encodeFamily (ranked p family)

def ExactRawRankLiteralShape : Prop :=
  ∀ (p : Pattern) (raw : RawFamily),
    (familyCode (p,raw)).map (List.map metadata) = raw.map (List.map metadata) ∧
    occurrences (familyCode (p,raw)) = (occurrences raw).map (rename p)

def ExactRawRankEffectivity : Prop := Primrec rankCode ∧ Primrec familyCode

def FullActualBitFamilyRawRank : Prop :=
  ExactRawRankCalibration ∧ ExactRawRankLiteralShape ∧ ExactRawRankEffectivity

end LogicLineages.PermittedControl.ActualBitFamilyRawRank
