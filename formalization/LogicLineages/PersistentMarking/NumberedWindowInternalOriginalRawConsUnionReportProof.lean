module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConsUnionReportBuildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenConsBuildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRawConsUnionReportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationValidityStackAppendListProof (appendZeroValue consBackward)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseFieldParser (parser prependResult prependPayload)
open NumberedWindowInternalSparseFieldParserTargets (parserGraph)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename parserRename)
open NumberedWindowInternalSparseFieldParserOpenChecks (exact_OpenNilRow)
open NumberedWindowInternalSparseFieldParserOpenConsBuildProof (consFromPrepend)
open NumberedWindowInternalDirectSourcePartitionRawTargets (ParsedTriplet)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalCertifiedUnionStepProof (unionGraph)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (unionGraphRename)
open NumberedWindowInternalConsUnionReportBuildProof (Report unionReportOfGraphs)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem prependSuccess (h t out : OTerm α)
    (packed : Report (B := B) (Γ := Γ) consCode out ![h,t]) :
    Report (B := B) (Γ := Γ) prependResult (suc out) ![h,suc t] := by
  let xs : Fin 2 → OTerm α := ![h,suc t]
  let cut : Program 2 := .composition predecessor (fun _ : Fin 1 => .projection 1)
  let write : Program 2 := .composition consCode ![.projection 0,cut]
  have usable : Report (B := B) (Γ := Γ) cut t xs := by
    apply compositionValue predecessor (fun _ : Fin 1 => .projection 1) t xs ![suc t]
      (predecessorSuccessor t)
    intro i
    exact projectionValue 1 xs
  have wrote : Report (B := B) (Γ := Γ) write out xs := by
    apply compositionValue consCode ![.projection 0,cut] out xs ![h,t] packed
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases usable (fun k => Fin.elim0 k)) i
  have row : Report (B := B) (Γ := Γ) prependPayload (suc out) xs := by
    apply compositionValue .succ (fun _ : Fin 1 => write) (suc out) xs ![out]
      (successorValue ![out])
    intro i
    obtain rfl := Fin.eq_zero i
    exact wrote
  exact successorBranchIntro (.projection 1) (constantZero 2) prependPayload (suc out) t xs
    (projectionValue 1 xs) row

theorem actualRawConsParser (h rawTail scratchTail out : OTerm α)
    (tail : Report (B := B) (Γ := Γ) parser (suc scratchTail) ![rawTail])
    (packed : Report (B := B) (Γ := Γ) consCode out ![h,scratchTail]) :
    Report (B := B) (Γ := Γ) parser (suc out) ![rawCons h rawTail] :=
  consFromPrepend (suc out) (rawCons h rawTail) h rawTail (suc scratchTail)
    (NumberedWindowInternalSparsePairGraphProof.consGraph h rawTail) tail
    (prependSuccess h scratchTail out packed)

/-- Only same-operand acceptance inside the *actual* object calculus.
Numerical observer fit is not a proof of this open graph. -/
def OpenObserverReflexivity (B : Positive (Fin 1)) (count : Program 2) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (scratch : OTerm α),
    Report (B := B) (Γ := Γ) count (suc z) ![scratch,scratch]

/-- One literal raw cons is the certified U of its literal raw singleton and
actual tail. Both fresh scratch outputs are produced by the actual cons
program. No converse parser or origin split is needed. -/
theorem exact_OriginalRawConsUnionReport (count : Program 2)
    (refl : OpenObserverReflexivity B count) (h tail scratch : OTerm α)
    (tailParse : Report (B := B) (Γ := Γ) parser (suc scratch) ![tail]) :
    Nonempty (Derivation B Γ (unionGraph count (rawCons h z) tail (rawCons h tail))) := by
  apply programCases consCode ![h,z] _
  intro β j Δ singletonOut keep single
  rw [binaryInputsRename,zRelabel] at single
  rw [unionGraphRename,rawConsRename,rawConsRename,zRelabel]
  have tail₁ : Report (B := B) (Γ := Δ) parser (suc (scratch.relabel j)) ![tail.relabel j] :=
    renameParser tail scratch tailParse j Δ keep
  apply programCases consCode ![h.relabel j,scratch.relabel j] _
  intro γ k Ξ parentOut keep' parent
  rw [binaryInputsRename] at parent
  rw [unionGraphRename,rawConsRename,rawConsRename,zRelabel]
  have tail₂ : Report (B := B) (Γ := Ξ) parser
      (suc ((scratch.relabel j).relabel k)) ![(tail.relabel j).relabel k] :=
    renameParser (tail.relabel j) (scratch.relabel j) tail₁ k Ξ keep'
  have left := renameInto single k Ξ keep'
  rw [ID1Completion.InternalControlGraphSupportProof.programRename,binaryInputsRename,zRelabel] at left
  let head₂ := (h.relabel j).relabel k
  let tail₂code := (tail.relabel j).relabel k
  let scratch₂ := (scratch.relabel j).relabel k
  let singleton₂ := singletonOut.relabel k
  obtain ⟨nil⟩ := exact_OpenNilRow B γ
  have nil₂ : Report (B := B) (Γ := Ξ) parser (suc z) ![z] :=
    ⟨weakenClosed nil Ξ⟩
  have parses : ParsedTriplet B Ξ (rawCons head₂ tail₂code) (rawCons head₂ z) tail₂code
      parentOut singleton₂ scratch₂ :=
    ⟨actualRawConsParser head₂ tail₂code scratch₂ parentOut tail₂ parent,
      actualRawConsParser head₂ z z singleton₂ nil₂ left, tail₂⟩
  have sameAppend := consBackward singleton₂ head₂ z scratch₂ scratch₂ parentOut
    left (appendZeroValue scratch₂) parent
  exact unionReportOfGraphs count (rawCons head₂ z) tail₂code (rawCons head₂ tail₂code)
    singleton₂ scratch₂ parentOut parentOut parses sameAppend (refl γ Ξ parentOut)

#print axioms actualRawConsParser
#print axioms exact_OriginalRawConsUnionReport

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRawConsUnionReportProof
