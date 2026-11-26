module
public import LogicLineages.PermittedControl.HighFieldComparisonTargets
public import LogicLineages.PermittedControl.InverseComparisonPreparedRowsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.HighFieldPreparedPacket
open OrdinalComparison FieldComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection

abbrev PostArgs := OrientedHighFormCode × Nat × Nat × Nat
abbrev Args := LongFieldCode × LongFieldCode × Nat × Nat × Nat

def lowerRank (orientation rankF rankG : Nat) : Nat :=
  if orientation = 0 then rankF else rankG

def sortedWanted (orientation wanted : Nat) : Nat :=
  if orientation = 0 then wanted else reverseComparisonCode wanted

def constantFormula (orientation answer wanted : Nat) : NormalForm.Formula :=
  if flipHighComparisonAnswer orientation answer = wanted then .truth else .falsity

/-- Keep the exact emitted lower operand code. A constant form has
an empty table, and a linear form has one genuine ordinary field request. -/
def postprocess (p : PostArgs) : PreparedPacketCode :=
  let (form,rankF,rankG,wanted) := p
  let (orientation,tag,answer,H) := form
  if wanted ≤ 2 then
    if tag = 0 then preparedPacketCode [] (constantFormula orientation answer wanted)
    else
      (Encodable.encode ([(1,lowerRank orientation rankF rankG,H)] : List LowerOperandCode),
        InverseComparisonPreparedRows.emitCode answer (sortedWanted orientation wanted))
  else preparedPacketCode [] .falsity

/-- This compiles on the actual chosen input ranks, before reading
the natural values of those ranks. -/
def compile (p : Args) : PreparedPacketCode :=
  let (F,G,rankF,rankG,wanted) := p
  postprocess (highRawComparisonForm F G rankF rankG,rankF,rankG,wanted)

def PostprocessEffective : Prop := Primrec postprocess

def PacketExact : Prop :=
  (∀ (form : OrientedHighFormCode) (rankF rankG wanted : Nat), 2 < wanted →
    postprocess (form,rankF,rankG,wanted) = preparedPacketCode [] .falsity) ∧
  (∀ (orientation c rankF rankG wanted : Nat), wanted ≤ 2 →
    postprocess ((orientation,rawConstForm c),rankF,rankG,wanted) =
      preparedPacketCode [] (constantFormula orientation c wanted)) ∧
  ∀ (orientation sign rankF rankG wanted : Nat) (H : ValueField), wanted ≤ 2 →
    postprocess ((orientation,rawLinearForm sign (longFieldCode H)),rankF,rankG,wanted) =
      preparedPacketCode [.ordinary (lowerRank orientation rankF rankG) H]
        (InverseComparisonPreparedRows.emitFormula sign (sortedWanted orientation wanted))

def PacketShape : Prop :=
  PreparedInput [] .falsity ∧
  (∀ orientation answer wanted, PreparedInput [] (constantFormula orientation answer wanted)) ∧
  ∀ (orientation sign rankF rankG wanted : Nat) (H : ValueField),
    PreparedInput [.ordinary (lowerRank orientation rankF rankG) H]
      (InverseComparisonPreparedRows.emitFormula sign (sortedWanted orientation wanted))

def FullHighFieldPreparedPostprocess : Prop :=
  PostprocessEffective ∧ PacketExact ∧ PacketShape

end LogicLineages.PermittedControl.HighFieldPreparedPacket
