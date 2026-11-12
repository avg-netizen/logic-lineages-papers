module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawErasureBottomInversionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawErasureBottomInversionConstructorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open OriginalTypedArgumentObservationsWalkQueryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] fold numberedConstructor

theorem lambdaTagAt (raw domain child : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child))) :
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) raw)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
 have ht := lambdaTag (.projection 0) raw domain child xs (projectionValue 0 xs) hc
 exact unaryRecover InternalUnpair.left (.projection 0) (numeral 1) raw xs ht (projectionValue 0 xs)

 theorem lambdaPreserved (raw out d k domain child : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
 (ho : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw))) :
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) out)) := by
 apply ternaryCases eraseRaw d (suc k) child _
 intro beta j Theta childOut hj hchild
 simp only [graph1Rename,numeralRename]
 have hc' := renameInto hc j Theta hj
 rw [graph2Rename] at hc'
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 rw [sucRelabel] at hchild
 have hout := OriginalRawSyntaxTransportInternalFoldLambdaProof.lambdaForward .erase (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j) (domain.relabel j) (child.relabel j) childOut hc' hchild ho'
 exact lambdaTagAt (out.relabel j) (domain.relabel j) childOut hout

theorem ordinaryTagAt (raw head child : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head child))) :
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 4) raw)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
 have ht := ordinaryTag (.projection 0) raw head child xs (projectionValue 0 xs) hc
 exact unaryRecover InternalUnpair.left (.projection 0) (numeral 4) raw xs ht (projectionValue 0 xs)

 theorem ordinaryPreserved (raw out d k head child : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head child)))
 (ho : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw))) :
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 4) out)) := by
 apply ternaryCases eraseRaw d (k) child _
 intro beta j Theta childOut hj hchild
 simp only [graph1Rename,numeralRename]
 have hc' := renameInto hc j Theta hj
 rw [graph2Rename] at hc'
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 have hout := OriginalRawSyntaxTransportInternalFoldOrdinaryProof.ordinaryForward .erase (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j) (head.relabel j) (child.relabel j) childOut hc' hchild ho'
 exact ordinaryTagAt (out.relabel j) (head.relabel j) childOut hout

theorem applicationTagAt (raw domain first second : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain first second))) :
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) raw)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
 have ht := applicationTag (.projection 0) raw domain first second xs (projectionValue 0 xs) hc
 exact unaryRecover InternalUnpair.left (.projection 0) (numeral 2) raw xs ht (projectionValue 0 xs)

 theorem applicationPreserved (raw out d k domain first second : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain first second)))
 (ho : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw))) :
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) out)) := by
 apply ternaryCases eraseRaw d (k) first _
 intro beta j Theta childOut hj hchild
 simp only [graph1Rename,numeralRename]
 have hc' := renameInto hc j Theta hj
 rw [graph3Rename] at hc'
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 apply ternaryCases eraseRaw (d.relabel j) (k.relabel j) (second.relabel j) _
 intro gamma l Xi otherOut hk hother
 simp only [graph1Rename,numeralRename]
 have hc'' := renameInto hc' l Xi hk
 rw [graph3Rename] at hc''
 have ho'' := renameInto ho' l Xi hk
 have hchild' := renameInto hchild l Xi hk
 rw [graph3Rename] at ho'' hchild'
 have hout := OriginalRawSyntaxTransportInternalFoldApplicationProof.applicationForward .erase ((raw.relabel j).relabel l) ((out.relabel j).relabel l) ((d.relabel j).relabel l) ((k.relabel j).relabel l) ((domain.relabel j).relabel l) ((first.relabel j).relabel l) ((second.relabel j).relabel l) (childOut.relabel l) otherOut hc'' hchild' hother ho''
 exact applicationTagAt ((out.relabel j).relabel l) ((domain.relabel j).relabel l) (childOut.relabel l) otherOut hout

theorem consTagAt (raw tau first second : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw tau first second))) :
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) raw)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
 have ht := consTag (.projection 0) raw tau first second xs (projectionValue 0 xs) hc
 exact unaryRecover InternalUnpair.left (.projection 0) (numeral 7) raw xs ht (projectionValue 0 xs)

 theorem consPreserved (raw out d k tau first second : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw tau first second)))
 (ho : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw))) :
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) out)) := by
 apply ternaryCases eraseRaw d (k) first _
 intro beta j Theta childOut hj hchild
 simp only [graph1Rename,numeralRename]
 have hc' := renameInto hc j Theta hj
 rw [graph3Rename] at hc'
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 apply ternaryCases eraseRaw (d.relabel j) (k.relabel j) (second.relabel j) _
 intro gamma l Xi otherOut hk hother
 simp only [graph1Rename,numeralRename]
 have hc'' := renameInto hc' l Xi hk
 rw [graph3Rename] at hc''
 have ho'' := renameInto ho' l Xi hk
 have hchild' := renameInto hchild l Xi hk
 rw [graph3Rename] at ho'' hchild'
 have hout := OriginalRawSyntaxTransportInternalFoldConsProof.consForward .erase ((raw.relabel j).relabel l) ((out.relabel j).relabel l) ((d.relabel j).relabel l) ((k.relabel j).relabel l) ((tau.relabel j).relabel l) ((first.relabel j).relabel l) ((second.relabel j).relabel l) (childOut.relabel l) otherOut hc'' hchild' hother ho''
 exact consTagAt ((out.relabel j).relabel l) ((tau.relabel j).relabel l) (childOut.relabel l) otherOut hout

theorem numberedTagAt (raw label head tau base types extras : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,base,types,extras]))) :
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) raw)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
 have ht := numberedTag (.projection 0) raw label head tau base types extras xs (projectionValue 0 xs) hc
 exact unaryRecover InternalUnpair.left (.projection 0) (numeral 5) raw xs ht (projectionValue 0 xs)

 theorem numberedPreserved (raw out d k label head tau base types extras : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,base,types,extras])))
 (ho : Nonempty (Derivation body Delta (graph3 eraseRaw out d k raw))) :
 Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) out)) := by
 apply ternaryCases eraseRaw d (k) base _
 intro beta j Theta childOut hj hchild
 simp only [graph1Rename,numeralRename]
 have hc' := renameInto hc j Theta hj
 rw [programRename] at hc'
 have hv1 : (fun i : Fin 6 => ((![label,head,tau,base,types,extras] : Fin 6 → OTerm alpha) i).relabel j) = ![(label.relabel j),(head.relabel j),(tau.relabel j),(base.relabel j),(types.relabel j),(extras.relabel j)] := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))))) i
 rw [hv1] at hc'
 have ho' := renameInto ho j Theta hj
 rw [graph3Rename] at ho'
 apply ternaryCases eraseRaw (d.relabel j) (k.relabel j) (extras.relabel j) _
 intro gamma l Xi otherOut hk hother
 simp only [graph1Rename,numeralRename]
 have hc'' := renameInto hc' l Xi hk
 rw [programRename] at hc''
 have hv2 : (fun i : Fin 6 => ((![(label.relabel j),(head.relabel j),(tau.relabel j),(base.relabel j),(types.relabel j),(extras.relabel j)] : Fin 6 → OTerm beta) i).relabel l) = ![((label.relabel j).relabel l),((head.relabel j).relabel l),((tau.relabel j).relabel l),((base.relabel j).relabel l),((types.relabel j).relabel l),((extras.relabel j).relabel l)] := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))))) i
 rw [hv2] at hc''
 have ho'' := renameInto ho' l Xi hk
 have hchild' := renameInto hchild l Xi hk
 rw [graph3Rename] at ho'' hchild'
 have hout := OriginalRawSyntaxTransportInternalFoldNumberedProof.numberedForward .erase ((raw.relabel j).relabel l) ((out.relabel j).relabel l) ((d.relabel j).relabel l) ((k.relabel j).relabel l) ((label.relabel j).relabel l) ((head.relabel j).relabel l) ((tau.relabel j).relabel l) ((base.relabel j).relabel l) ((types.relabel j).relabel l) ((extras.relabel j).relabel l) (childOut.relabel l) otherOut hc'' hchild' hother ho''
 exact numberedTagAt ((out.relabel j).relabel l) ((label.relabel j).relabel l) ((head.relabel j).relabel l) ((tau.relabel j).relabel l) (childOut.relabel l) ((types.relabel j).relabel l) otherOut hout
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawErasureBottomInversionConstructorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawErasureBottomInversionConstructorProof
