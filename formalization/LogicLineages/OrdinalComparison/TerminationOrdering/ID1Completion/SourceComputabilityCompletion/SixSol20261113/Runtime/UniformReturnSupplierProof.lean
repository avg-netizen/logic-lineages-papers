module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnPartitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSupplierProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof
open InternalAcceptanceSupportProof (programCases)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename consTermRename)
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Proof-local uniform selector interface, not a replacement source admission
or a premise in the frozen public endpoint. All four graphs are actual original
programs. Its supplier is constructed from length and actual queries below. -/
def Supplier (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha))
 (children deletions produced first second row : OTerm alpha) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (old results : OTerm beta),
 (∀ f ∈ Delta, f.relabel j ∈ Theta) →
 Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append results (produced.relabel j) old)) →
 Nonempty (Derivation body Theta
  (graph3 OriginalHereditaryResultStackProgram.firstSlot (first.relabel j) (children.relabel j) (deletions.relabel j) results ⊓
  (graph3 OriginalHereditaryResultStackProgram.secondSlot (second.relabel j) (children.relabel j) (deletions.relabel j) results ⊓
  (graph3 OriginalHereditaryResultStackProgram.deletionRow (row.relabel j) (children.relabel j) (deletions.relabel j) results ⊓
   graph3 OriginalHereditaryResultStackProgram.oldSuffix old (children.relabel j) (deletions.relabel j) results))))
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem supplierRename {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
 (children deletions produced first second row : OTerm alpha)
 (hi : ∀ f ∈ Delta, f.relabel j ∈ Theta)
 (hs : Supplier body Delta children deletions produced first second row) :
 Supplier body Theta (children.relabel j) (deletions.relabel j) (produced.relabel j)
   (first.relabel j) (second.relabel j) (row.relabel j) := by
 intro gamma k Xi old results hk ha
 have inc : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Xi := by
   intro f hf
   simpa only [← formulaRelabelComposition] using hk _ (hi f hf)
 have ha' : Nonempty (Derivation body Xi
   (graph2 InternalApplicationValidityStackAppend.append results (produced.relabel (k ∘ j)) old)) := by
   simpa only [Term.relabel_relabel] using ha
 have h := hs gamma (k ∘ j) Xi old results inc ha'
 simpa only [Term.relabel_relabel] using h
/-- A real deletion partition and background-stable child slots supply all
four actual return selectors. No output stack shape is postulated. -/
theorem fromData (children deletions produced front childRow first second row : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add children deletions) produced)))
 (hf : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions front)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front childRow)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse row front)))
 (slots : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (old results : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append results (produced.relabel j) old)) →
   Nonempty (Derivation body Theta
     (graph3 OriginalHereditaryResultStackProgram.firstSlot (first.relabel j) (children.relabel j) (deletions.relabel j) results ⊓
      graph3 OriginalHereditaryResultStackProgram.secondSlot (second.relabel j) (children.relabel j) (deletions.relabel j) results))) :
 Supplier body Delta children deletions produced first second row := by
 intro beta j Theta old results hi ha
 have hl' := renameInto hl j Theta hi
 have hf' := renameInto hf j Theta hi
 have hp' := renameInto hp j Theta hi
 have hr' := renameInto hr j Theta hi
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,
   graph1Rename,graph2Rename] at hl' hf' hp' hr'
 have hs := slots beta j Theta old results hi ha
 have hold := UniformReturnStackProof.oldSuffix (children.relabel j) (deletions.relabel j)
   (produced.relabel j) old results hl' ha
 apply programCases InternalApplicationValidityStackAppend.append (Fin.cons (childRow.relabel j) (Fin.cons old Fin.elim0)) _
 intro gamma k Xi childOld hk hc
 simp only [consTermRename,emptyRename] at hc
 have hf'' := renameInto hf' k Xi hk
 have hp'' := renameInto hp' k Xi hk
 have hr'' := renameInto hr' k Xi hk
 have ha' := renameInto ha k Xi hk
 have hs' := renameInto hs k Xi hk
 have hold' := renameInto hold k Xi hk
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,graph1Rename,graph2Rename,
   graph3Rename,conjunctionRename] at hf'' hp'' hr'' ha' hs' hold' ⊢
 have hfront := UniformReturnStackProof.deletionFront ((deletions.relabel j).relabel k)
   ((front.relabel j).relabel k) ((childRow.relabel j).relabel k) ((produced.relabel j).relabel k)
   (old.relabel k) childOld (results.relabel k) hf'' hp'' hc ha'
 have hrow := UniformReturnSlotsProof.deletionRow ((children.relabel j).relabel k)
   ((deletions.relabel j).relabel k) (results.relabel k) ((front.relabel j).relabel k)
   ((row.relabel j).relabel k) hfront hr''
 exact andIntro (andLeft hs') (andIntro (andRight hs') (andIntro hrow hold'))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSupplierProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSupplierProof
