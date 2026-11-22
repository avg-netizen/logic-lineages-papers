module
public import LogicLineages.PermittedControl.StageCallbackRenderLinearTargets
public import LogicLineages.PermittedControl.ActualGreatestCongruenceRouteTargets

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackRender
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperandCode PreparedPacketCode)
open RawPacketAlgebra (encodePacket)
open MixedSameRankResidue (WeightedCode)
open MixedRankResidue (rankSupportCode)
open RankResidueChoices (namedSlots)
open MixedRankNamedResidueRow (RawArgs)
open SharedRankResidueRow (Layout formulaCode)
open ActualRawSignedStaticCeiling (RawSyntax encodeSyntax)
open ActualSymbolicZeroSuccessor (SyntaxState)

/-- The accepted literal rank support of the raw terms, kept below `top`. -/
def lowerRanksCode (top : Nat) (ts : List WeightedCode) : List Nat :=
  (rankSupportCode ts).foldr (fun rank rest => if rank < top then rank :: rest else rest) []

/-- Operand code of a bare raw coordinate. -/
def coordinateCode (rank : Nat) : LowerOperandCode :=
  ((0 : Nat),rank,((0 : Nat),(0 : Nat),(0 : Nat),(0 : Nat)))

/-- Raw congruence packet: one coordinate slot per lower rank; the
accepted residue-row formula code on the layout that reserves name zero
for the greatest rank; then the requested polarity. -/
def modularCode (top m : Nat) (s : RawSyntax) (positive : Bool) : PreparedPacketCode :=
  (Encodable.encode ((lowerRanksCode top s.2).map coordinateCode),
    polarityCode
      (formulaCode ((0,top) :: namedSlots (lowerRanksCode top s.2)) (m,s.1,s.2)) positive)

/-- The `modular` field of `Rendering.Exact`, for this program, for every
modulus including zero. -/
def ExactModularCode : Prop :=
  ∀ (top m : Nat) (s : SyntaxState) (positive : Bool),
    modularCode top m (encodeSyntax s) positive =
      encodePacket (ActualGreatestCongruenceRoute.packet top m s positive)

def ModularCodeEffectivity : Prop :=
  Primrec₂ lowerRanksCode ∧
  Primrec (fun p : Layout × RawArgs => formulaCode p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × RawSyntax × Bool => modularCode p.1 p.2.1 p.2.2.1 p.2.2.2)

def FullStageCallbackRenderModular : Prop := ExactModularCode ∧ ModularCodeEffectivity

end LogicLineages.PermittedControl.StageCallbackRender
