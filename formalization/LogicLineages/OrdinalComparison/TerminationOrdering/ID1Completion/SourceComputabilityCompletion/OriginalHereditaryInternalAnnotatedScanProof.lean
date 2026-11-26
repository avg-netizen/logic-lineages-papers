module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanIndexedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof (unaryValue)
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalApplicationStepPeelSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalHereditaryAnnotatedExpansion (scan decorateAll decorate)
open OriginalHereditaryInternalAnnotatedScanDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem scanFromAll (role typ raw jobs output count : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph4 decorateAll output role typ raw jobs)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count jobs))) :
 Nonempty (Derivation body Delta (graph5 scan output count role typ raw jobs)) := by
 let xs : Fin 4 → OTerm alpha := Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0)))
 apply compositionRecover scan _ output xs
   (Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))) ha
 intro i
 exact Fin.cases
   (unaryValue length (.projection 3) count jobs xs hl (projectionValue 3 xs))
   (Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
     (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs) (fun k => Fin.elim0 k))))) i

theorem actualLookup : OriginalHereditaryInternalAnnotatedScanTargets.ActualLookup := by
 intro body alpha Delta role typ raw jobs output count index child psi ha hl hb hv next
 apply programCases length (Fin.cons jobs Fin.elim0) _
 intro beta j Theta rawLength hj hlen
 have ha' := renameInto ha j Theta hj
 rw [graph4Rename] at ha'
 have hl' := renameInto hl j Theta hj
 rw [lengthRename] at hl'
 simp only [consTermRename,emptyRename] at hlen
 have hscan := scanFromAll (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j)
   (output.relabel j) rawLength ha' hlen
 have houtlen := OriginalHereditaryInternalAnnotatedScanLengthProof.scanLength
   rawLength (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j) (output.relabel j) hscan
 have he := valueUnique length rawLength (count.relabel j) (Fin.cons (output.relabel j) Fin.elim0) houtlen hl'
 have hactualLen := outputTransport length rawLength (count.relabel j)
   (Fin.cons (jobs.relabel j) Fin.elim0) he hlen
 change Nonempty (Derivation body Theta (lengthGraph (count.relabel j) (jobs.relabel j))) at hactualLen
 have hactualScan := scanFromAll (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j)
   (output.relabel j) (count.relabel j) ha' hactualLen
 have hb' := renameInto hb j Theta hj
 simp only [Below,InternalOriginalOrderSyntaxProof.orderRename] at hb'
 have hv' := renameInto hv j Theta hj
 rw [graph2Rename] at hv'
 have hcell := OriginalHereditaryInternalAnnotatedScanIndexedProof.actualIndexed body beta Theta
   (count.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j)
   (output.relabel j) (index.relabel j) (child.relabel j) hactualScan hb' hv'
 apply programCases InternalRawListRecursion.lookup
   (Fin.cons (index.relabel j) (Fin.cons (jobs.relabel j) Fin.elim0)) _
 intro gamma k Xi rawChild hk hlookup
 have hcell' := renameInto hcell k Xi hk
 rw [graph5Rename] at hcell'
 have hlen' := renameInto hactualLen k Xi hk
 rw [lengthRename] at hlen'
 simp only [consTermRename,emptyRename] at hlookup
 have hd := OriginalHereditaryInternalAnnotatedScanLengthStepProof.cellRecover
   ((index.relabel j).relabel k) ((role.relabel j).relabel k) ((typ.relabel j).relabel k)
   ((raw.relabel j).relabel k) ((jobs.relabel j).relabel k) ((child.relabel j).relabel k)
   rawChild hcell' hlookup
 have result := next gamma (k ∘ j) Xi rawChild
   (by intro f hf; simpa only [← InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk _ (hj f hf))
   (by simpa only [Term.relabel_relabel] using hlen')
   (by simpa only [Term.relabel_relabel] using hlookup)
   (by simpa only [Term.relabel_relabel] using hd)
 simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using result

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanProof
