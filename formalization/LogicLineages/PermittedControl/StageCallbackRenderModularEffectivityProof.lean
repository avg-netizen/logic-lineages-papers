module
public import LogicLineages.PermittedControl.StageCallbackRenderModularTargets
import LogicLineages.PermittedControl.MixedRankNamedResidueRowSyntaxCodeProof
import LogicLineages.PermittedControl.MixedRankResidueStatementChecks
import LogicLineages.PermittedControl.RankResidueChoicesStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackRender
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof (add_primitive abs_primitive)
open PreparedProjection (LowerOperandCode PreparedPacketCode)
open MixedSameRankResidue (WeightedCode)
open MixedRankResidue (rankSupportCode residueVectorCode)
open RankResidueChoices (Slot Digit Cell namedSlots choices)
open MixedRankNamedResidueRow (RawArgs toVector clauseCode clauseCodePrimitive)
open MixedNamedResidueRow (keep)
open SharedRankResidueRow (Layout formulaCode)
open StatementChecks (fixed_mixedRankResidueCodeExact fixed_rankResidueLayoutAndChoices)
open ActualRawSignedStaticCeiling (RawSyntax)

theorem lowerRanksPrimitive : Primrec₂ lowerRanksCode := by
  let A := Nat × List WeightedCode
  have support : Primrec (fun q : A => rankSupportCode q.2) :=
    fixed_mixedRankResidueCodeExact.1.comp Primrec.snd
  have step : Primrec (fun q : A × (Nat × List Nat) =>
      if q.2.1 < q.1.1 then q.2.1 :: q.2.2 else q.2.2) :=
    Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have fold : Primrec (fun q : A => (rankSupportCode q.2).foldr
      (fun rank rest => if rank < q.1 then rank :: rest else rest) []) :=
    Primrec.list_foldr support (Primrec.const []) step.to₂
  exact fold.to₂

theorem formulaStepPrimitive :
    Primrec₂ (fun (p : Layout × RawArgs) (z : Cell × Nat) =>
      if keep p.2.1 (p.2.2.1 + residueVectorCode p.2.2.2 (toVector z.1)) then
        6 * Nat.pair (clauseCode p.2.1 z.1) z.2 + 5 else z.2) := by
  let Step := (Layout × RawArgs) × (Cell × Nat)
  have raw : Primrec (fun p : Step => p.1.2) := Primrec.snd.comp Primrec.fst
  have modulus : Primrec (fun p : Step => p.1.2.1) := Primrec.fst.comp raw
  have constant : Primrec (fun p : Step => p.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp raw)
  have terms : Primrec (fun p : Step => p.1.2.2.2) := Primrec.snd.comp (Primrec.snd.comp raw)
  have cell : Primrec (fun p : Step => p.2.1) := Primrec.fst.comp Primrec.snd
  have tail : Primrec (fun p : Step => p.2.2) := Primrec.snd.comp Primrec.snd
  have entry : Primrec (fun p : Cell × Digit => p.2.2) := Primrec.snd.comp Primrec.snd
  have vector : Primrec toVector := Primrec.list_map Primrec.id entry.to₂
  have sum := add_primitive.comp constant
    (fixed_mixedRankResidueCodeExact.2.1.comp terms (vector.comp cell))
  have retained : PrimrecPred (fun p : Step => keep p.1.2.1
      (p.1.2.2.1 + residueVectorCode p.1.2.2.2 (toVector p.2.1)) = true) := by
    simpa only [keep,decide_eq_true_eq] using
      Primrec.eq.comp (Primrec.nat_mod.comp (abs_primitive.comp sum) modulus) (Primrec.const 0)
  have disjunction := Primrec₂.natPair.comp (clauseCodePrimitive.comp modulus cell) tail
  have next := Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6) disjunction) (Primrec.const 5)
  exact Primrec.ite retained next tail

theorem formulaPrimitive : Primrec (fun p : Layout × RawArgs => formulaCode p.1 p.2) := by
  have layout : Primrec (Prod.fst : Layout × RawArgs → Layout) := Primrec.fst
  have modulus : Primrec (fun p : Layout × RawArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have cells := fixed_rankResidueLayoutAndChoices.2.1.comp modulus layout
  exact Primrec.list_foldr cells (Primrec.const 1) formulaStepPrimitive

theorem coordinatePrimitive : Primrec coordinateCode :=
  (Primrec.const (0 : Nat)).pair
    (Primrec.id.pair (Primrec.const ((0 : Nat),(0 : Nat),(0 : Nat),(0 : Nat))))

theorem polarityPrimitive : Primrec₂ polarityCode :=
  (Primrec.cond Primrec.snd Primrec.fst
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.fst)
      (Primrec.const 3))).to₂

attribute [local irreducible] lowerRanksCode formulaCode namedSlots coordinateCode polarityCode

/-- Table bytes from the list of lower ranks. -/
theorem tableBytesPrimitive :
    Primrec (fun ranks : List Nat => Encodable.encode (ranks.map coordinateCode)) :=
  Primrec.encode.comp (Primrec.list_map Primrec.id (coordinatePrimitive.comp Primrec.snd).to₂)

/-- Formula code from the greatest rank, the lower ranks and the raw row. -/
theorem layoutFormulaPrimitive :
    Primrec (fun q : (Nat × List Nat) × RawArgs =>
      formulaCode ((0,q.1.1) :: namedSlots q.1.2) q.2) := by
  have slots : Primrec (fun q : (Nat × List Nat) × RawArgs =>
      (((0 : Nat),q.1.1) : Slot) :: namedSlots q.1.2) :=
    Primrec.list_cons.comp ((Primrec.const (0 : Nat)).pair (Primrec.fst.comp Primrec.fst))
      (fixed_rankResidueLayoutAndChoices.1.comp (Primrec.snd.comp Primrec.fst))
  exact formulaPrimitive.comp (slots.pair Primrec.snd)

theorem modularPrimitive :
    Primrec (fun p : Nat × Nat × RawSyntax × Bool => modularCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := Nat × Nat × RawSyntax × Bool
  have source : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have terms : Primrec (fun p : A => p.2.2.1.2) := Primrec.snd.comp source
  have ranks : Primrec (fun p : A => lowerRanksCode p.1 p.2.2.1.2) :=
    lowerRanksPrimitive.comp Primrec.fst terms
  have table : Primrec (fun p : A =>
      Encodable.encode ((lowerRanksCode p.1 p.2.2.1.2).map coordinateCode)) :=
    tableBytesPrimitive.comp ranks
  have args : Primrec (fun p : A => ((p.2.1,p.2.2.1.1,p.2.2.1.2) : RawArgs)) :=
    (Primrec.fst.comp Primrec.snd).pair ((Primrec.fst.comp source).pair terms)
  have code : Primrec (fun p : A =>
      formulaCode ((0,p.1) :: namedSlots (lowerRanksCode p.1 p.2.2.1.2))
        (p.2.1,p.2.2.1.1,p.2.2.1.2)) :=
    layoutFormulaPrimitive.comp ((Primrec.fst.pair ranks).pair args)
  have polarity : Primrec (fun p : A =>
      polarityCode (formulaCode ((0,p.1) :: namedSlots (lowerRanksCode p.1 p.2.2.1.2))
        (p.2.1,p.2.2.1.1,p.2.2.1.2)) p.2.2.2) :=
    polarityPrimitive.comp code (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact table.pair polarity

theorem modularCodeEffectivity : ModularCodeEffectivity :=
  ⟨lowerRanksPrimitive,formulaPrimitive,modularPrimitive⟩

end LogicLineages.PermittedControl.StageCallbackRender
