module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.ConstructorFoldProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.FilterStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.AssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open OriginalRawSyntaxTransport
open SupportProof ConstructorFoldProof

def casesPart : Program 2 := .composition OriginalSourceHeads.casesRecursors (fun _ : Fin 1 => .projection 1)
def appPart : Program 2 := .composition OriginalSourceHeads.applications (fun _ : Fin 1 => .projection 1)
def rankedPart : Program 2 := .composition OriginalSourceHeads.rankedHeads (fun _ : Fin 1 => .projection 0)
def middle : Program 2 := .composition InternalApplicationValidityStackAppend.append ![appPart,rankedPart]
def tail : Program 2 := .composition InternalApplicationValidityStackAppend.append ![casesPart,middle]
def zeroHead : Program 2 := pairOf (constant 2 0) (constant 2 0)
def succHead : Program 2 := pairOf (constant 2 1) (constant 2 0)

theorem tailLift (out list needle symbols types : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 tail list symbols types)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) list needle)))
    (ho : Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.rawWindow out symbols types))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) :=
  doubleTail zeroHead succHead tail out list needle (Fin.cons symbols (Fin.cons types Fin.elim0)) hl hm ho

theorem casesLift (out list needle symbols types : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 casesPart list symbols types)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) list needle)))
    (ho : Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.rawWindow out symbols types))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) := by
  apply programCases tail (Fin.cons symbols (Fin.cons types Fin.elim0)) _
  intro beta j Theta rest hj hr
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hr
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hlj := renameInto hl j Theta hj
  have hmj := renameInto hm j Theta hj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hlj hmj hoj
  exact tailLift (out.relabel j) rest (needle.relabel j) (symbols.relabel j) (types.relabel j) hr
    (appendLeft casesPart middle rest (list.relabel j) (needle.relabel j)
      (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0)) hlj hmj hr) hoj

theorem middleLift (out list needle symbols types : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 middle list symbols types)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) list needle)))
    (ho : Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.rawWindow out symbols types))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) := by
  apply programCases tail (Fin.cons symbols (Fin.cons types Fin.elim0)) _
  intro beta j Theta rest hj hr
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hr
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hlj := renameInto hl j Theta hj
  have hmj := renameInto hm j Theta hj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hlj hmj hoj
  exact tailLift (out.relabel j) rest (needle.relabel j) (symbols.relabel j) (types.relabel j) hr
    (appendRight casesPart middle rest (list.relabel j) (needle.relabel j)
      (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0)) hlj hmj hr) hoj

theorem applicationLift (out list needle symbols types : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 appPart list symbols types)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) list needle)))
    (ho : Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.rawWindow out symbols types))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) := by
  apply programCases middle (Fin.cons symbols (Fin.cons types Fin.elim0)) _
  intro beta j Theta rest hj hr
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hr
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hlj := renameInto hl j Theta hj
  have hmj := renameInto hm j Theta hj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hlj hmj hoj
  exact middleLift (out.relabel j) rest (needle.relabel j) (symbols.relabel j) (types.relabel j) hr
    (appendLeft appPart rankedPart rest (list.relabel j) (needle.relabel j)
      (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0)) hlj hmj hr) hoj

theorem rankedLift (out list needle symbols types : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 rankedPart list symbols types)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) list needle)))
    (ho : Nonempty (Derivation body Delta (graph2 OriginalSourceHeads.rawWindow out symbols types))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) := by
  apply programCases middle (Fin.cons symbols (Fin.cons types Fin.elim0)) _
  intro beta j Theta rest hj hr
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hr
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hlj := renameInto hl j Theta hj
  have hmj := renameInto hm j Theta hj
  have hoj := renameInto ho j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hlj hmj hoj
  exact middleLift (out.relabel j) rest (needle.relabel j) (symbols.relabel j) (types.relabel j) hr
    (appendRight appPart rankedPart rest (list.relabel j) (needle.relabel j)
      (Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0)) hlj hmj hr) hoj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.AssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.AssemblyProof
