module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorLayerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenProjectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentBranchesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentArrowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTypesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open EvaluatorChildrenProjectionProof
theorem types0 (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter out lt rt : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 0) left parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 0) right parameter)))
 (hvl : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out left parameter)))
 (hvr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out right parameter)))
 (hyl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left lt left)))
 (hyr : Nonempty (Derivation body Delta (graph1 InternalUnpair.left rt right))) :
 Nonempty (Derivation body Delta (equal lt rt)) := by
 let q0 : Program 1 := rightOf (.projection 0)
 let q1 : Program 1 := leftOf q0
 let q2 : Program 1 := rightOf q0
 let q3 : Program 1 := leftOf q2
 let qs : Fin 4 → Program 1 := ![q0,q1,q2,q3]
 let xs : Fin 1 → OTerm alpha := ![out]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 have hx : (fun i => (xs i).relabel j) = (![out.relabel j] : Fin 1 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 let xx : Fin 1 → OTerm beta := ![out.relabel j]
 have h0 := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx (hq 0) (projectionValue 0 xx)
 have h1 := unaryRecover InternalUnpair.left q0 (ys 1) (ys 0) xx (hq 1) (hq 0)
 have h2 := unaryRecover InternalUnpair.right q0 (ys 2) (ys 0) xx (hq 2) (hq 0)
 have h3 := unaryRecover InternalUnpair.left q2 (ys 3) (ys 2) xx (hq 3) (hq 2)
 have hsl' := renameInto hsl j Theta hj
 have hsr' := renameInto hsr j Theta hj
 have htl' := renameInto htl j Theta hj
 have htr' := renameInto htr j Theta hj
 have hvl' := renameInto hvl j Theta hj
 have hvr' := renameInto hvr j Theta hj
 have hyl' := renameInto hyl j Theta hj
 have hyr' := renameInto hyr j Theta hj
 simp only [graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' htl' htr' hvl' hvr' hyl' hyr'
 have hbl := EvaluatorAlignmentBranchesProof.branch0 R (left.relabel j) (parameter.relabel j) (out.relabel j) htl' hvl'
 have hdl := rightComponent _ _ (left.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) h0 hbl
 have tyl := leftComponent _ _ (left.relabel j) (parameter.relabel j) (ys 0) (ys 1) h1 hdl
 have inpl := EvaluatorChildrenSelectorWiring.resultType body beta Theta (lt.relabel j) (left.relabel j) (parameter.relabel j) hyl'
 have eql := valueUnique OriginalRootObservation.resultType (lt.relabel j) (ys 1) (![ left.relabel j,parameter.relabel j]) inpl tyl
 have hbr := EvaluatorAlignmentBranchesProof.branch0 R (right.relabel j) (parameter.relabel j) (out.relabel j) htr' hvr'
 have hdr := rightComponent _ _ (right.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) h0 hbr
 have tyr := leftComponent _ _ (right.relabel j) (parameter.relabel j) (ys 0) (ys 1) h1 hdr
 have inpr := EvaluatorChildrenSelectorWiring.resultType body beta Theta (rt.relabel j) (right.relabel j) (parameter.relabel j) hyr'
 have eqr := valueUnique OriginalRootObservation.resultType (rt.relabel j) (ys 1) (![ right.relabel j,parameter.relabel j]) inpr tyr
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
 obtain ⟨el⟩ := eql
 obtain ⟨er⟩ := eqr
 exact ⟨InternalTagArithmeticSupportProof.trans el (InternalTagArithmeticSupportProof.symm er)⟩

theorem types1 (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter out lt rt : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) left parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) right parameter)))
 (hvl : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out left parameter)))
 (hvr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out right parameter)))
 (hyl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left lt left)))
 (hyr : Nonempty (Derivation body Delta (graph1 InternalUnpair.left rt right))) :
 Nonempty (Derivation body Delta (equal lt rt)) := by
 let q0 : Program 1 := rightOf (.projection 0)
 let q1 : Program 1 := leftOf q0
 let q2 : Program 1 := rightOf q0
 let q3 : Program 1 := leftOf q2
 let qs : Fin 4 → Program 1 := ![q0,q1,q2,q3]
 let xs : Fin 1 → OTerm alpha := ![out]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 have hx : (fun i => (xs i).relabel j) = (![out.relabel j] : Fin 1 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 let xx : Fin 1 → OTerm beta := ![out.relabel j]
 have h0 := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx (hq 0) (projectionValue 0 xx)
 have h1 := unaryRecover InternalUnpair.left q0 (ys 1) (ys 0) xx (hq 1) (hq 0)
 have h2 := unaryRecover InternalUnpair.right q0 (ys 2) (ys 0) xx (hq 2) (hq 0)
 have h3 := unaryRecover InternalUnpair.left q2 (ys 3) (ys 2) xx (hq 3) (hq 2)
 have hsl' := renameInto hsl j Theta hj
 have hsr' := renameInto hsr j Theta hj
 have htl' := renameInto htl j Theta hj
 have htr' := renameInto htr j Theta hj
 have hvl' := renameInto hvl j Theta hj
 have hvr' := renameInto hvr j Theta hj
 have hyl' := renameInto hyl j Theta hj
 have hyr' := renameInto hyr j Theta hj
 simp only [graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' htl' htr' hvl' hvr' hyl' hyr'
 have fieldsl := EvaluatorAlignmentFieldsProof.lambdaAt R (left.relabel j) (parameter.relabel j)
   (out.relabel j) (ys 0) (ys 2) (ys 1) (ys 3) htl' hvl' h0 h1 h2 h3
 have tyl := EvaluatorAlignmentArrowProof.sourceArrow H G M W (left.relabel j) (parameter.relabel j)
   (lt.relabel j) (ys 1) (ys 3) hsl' htl' hyl' (andLeft fieldsl) (andRight fieldsl)
 have fieldsr := EvaluatorAlignmentFieldsProof.lambdaAt R (right.relabel j) (parameter.relabel j)
   (out.relabel j) (ys 0) (ys 2) (ys 1) (ys 3) htr' hvr' h0 h1 h2 h3
 have tyr := EvaluatorAlignmentArrowProof.sourceArrow H G M W (right.relabel j) (parameter.relabel j)
   (rt.relabel j) (ys 1) (ys 3) hsr' htr' hyr' (andLeft fieldsr) (andRight fieldsr)
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
 exact valueUnique OriginalLambdaConstructor.arrow (lt.relabel j) (rt.relabel j) (![ys 1,ys 3]) tyl tyr

theorem types2 (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter out lt rt : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) left parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) right parameter)))
 (hvl : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out left parameter)))
 (hvr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out right parameter)))
 (hyl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left lt left)))
 (hyr : Nonempty (Derivation body Delta (graph1 InternalUnpair.left rt right))) :
 Nonempty (Derivation body Delta (equal lt rt)) := by
 let q0 : Program 1 := rightOf (.projection 0)
 let q1 : Program 1 := leftOf q0
 let q2 : Program 1 := rightOf q0
 let q3 : Program 1 := leftOf q2
 let qs : Fin 4 → Program 1 := ![q0,q1,q2,q3]
 let xs : Fin 1 → OTerm alpha := ![out]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 have hx : (fun i => (xs i).relabel j) = (![out.relabel j] : Fin 1 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 let xx : Fin 1 → OTerm beta := ![out.relabel j]
 have h0 := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx (hq 0) (projectionValue 0 xx)
 have h1 := unaryRecover InternalUnpair.left q0 (ys 1) (ys 0) xx (hq 1) (hq 0)
 have h2 := unaryRecover InternalUnpair.right q0 (ys 2) (ys 0) xx (hq 2) (hq 0)
 have h3 := unaryRecover InternalUnpair.left q2 (ys 3) (ys 2) xx (hq 3) (hq 2)
 have hsl' := renameInto hsl j Theta hj
 have hsr' := renameInto hsr j Theta hj
 have htl' := renameInto htl j Theta hj
 have htr' := renameInto htr j Theta hj
 have hvl' := renameInto hvl j Theta hj
 have hvr' := renameInto hvr j Theta hj
 have hyl' := renameInto hyl j Theta hj
 have hyr' := renameInto hyr j Theta hj
 simp only [graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' htl' htr' hvl' hvr' hyl' hyr'
 have hbl := EvaluatorChildrenProjectionProof.applicationBranch R (left.relabel j) (parameter.relabel j) (out.relabel j) htl' hvl'
 have hdl := rightComponent _ _ (left.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) h0 hbl
 have restl := rightComponent _ _ (left.relabel j) (parameter.relabel j) (ys 0) (ys 2) h2 hdl
 have tyl := leftComponent _ _ (left.relabel j) (parameter.relabel j) (ys 2) (ys 3) h3 restl
 have inpl := EvaluatorChildrenSelectorWiring.resultType body beta Theta (lt.relabel j) (left.relabel j) (parameter.relabel j) hyl'
 have eql := valueUnique OriginalRootObservation.resultType (lt.relabel j) (ys 3) (![ left.relabel j,parameter.relabel j]) inpl tyl
 have hbr := EvaluatorChildrenProjectionProof.applicationBranch R (right.relabel j) (parameter.relabel j) (out.relabel j) htr' hvr'
 have hdr := rightComponent _ _ (right.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) h0 hbr
 have restr := rightComponent _ _ (right.relabel j) (parameter.relabel j) (ys 0) (ys 2) h2 hdr
 have tyr := leftComponent _ _ (right.relabel j) (parameter.relabel j) (ys 2) (ys 3) h3 restr
 have inpr := EvaluatorChildrenSelectorWiring.resultType body beta Theta (rt.relabel j) (right.relabel j) (parameter.relabel j) hyr'
 have eqr := valueUnique OriginalRootObservation.resultType (rt.relabel j) (ys 3) (![ right.relabel j,parameter.relabel j]) inpr tyr
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
 obtain ⟨el⟩ := eql
 obtain ⟨er⟩ := eqr
 exact ⟨InternalTagArithmeticSupportProof.trans el (InternalTagArithmeticSupportProof.symm er)⟩

theorem types3 (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter out lt rt : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 3) left parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 3) right parameter)))
 (hvl : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out left parameter)))
 (hvr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out right parameter)))
 (hyl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left lt left)))
 (hyr : Nonempty (Derivation body Delta (graph1 InternalUnpair.left rt right))) :
 Nonempty (Derivation body Delta (equal lt rt)) := by
 let q0 : Program 1 := rightOf (.projection 0)
 let q1 : Program 1 := leftOf q0
 let q2 : Program 1 := rightOf q0
 let q3 : Program 1 := leftOf q2
 let qs : Fin 4 → Program 1 := ![q0,q1,q2,q3]
 let xs : Fin 1 → OTerm alpha := ![out]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 have hx : (fun i => (xs i).relabel j) = (![out.relabel j] : Fin 1 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 let xx : Fin 1 → OTerm beta := ![out.relabel j]
 have h0 := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx (hq 0) (projectionValue 0 xx)
 have h1 := unaryRecover InternalUnpair.left q0 (ys 1) (ys 0) xx (hq 1) (hq 0)
 have h2 := unaryRecover InternalUnpair.right q0 (ys 2) (ys 0) xx (hq 2) (hq 0)
 have h3 := unaryRecover InternalUnpair.left q2 (ys 3) (ys 2) xx (hq 3) (hq 2)
 have hsl' := renameInto hsl j Theta hj
 have hsr' := renameInto hsr j Theta hj
 have htl' := renameInto htl j Theta hj
 have htr' := renameInto htr j Theta hj
 have hvl' := renameInto hvl j Theta hj
 have hvr' := renameInto hvr j Theta hj
 have hyl' := renameInto hyl j Theta hj
 have hyr' := renameInto hyr j Theta hj
 simp only [graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' htl' htr' hvl' hvr' hyl' hyr'
 have hbl := EvaluatorAlignmentBranchesProof.branch3 R (left.relabel j) (parameter.relabel j) (out.relabel j) htl' hvl'
 have hdl := rightComponent _ _ (left.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) h0 hbl
 have tyl := hdl
 have inpl := EvaluatorChildrenSelectorWiring.resultType body beta Theta (lt.relabel j) (left.relabel j) (parameter.relabel j) hyl'
 have eql := valueUnique OriginalRootObservation.resultType (lt.relabel j) (ys 0) (![ left.relabel j,parameter.relabel j]) inpl tyl
 have hbr := EvaluatorAlignmentBranchesProof.branch3 R (right.relabel j) (parameter.relabel j) (out.relabel j) htr' hvr'
 have hdr := rightComponent _ _ (right.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) h0 hbr
 have tyr := hdr
 have inpr := EvaluatorChildrenSelectorWiring.resultType body beta Theta (rt.relabel j) (right.relabel j) (parameter.relabel j) hyr'
 have eqr := valueUnique OriginalRootObservation.resultType (rt.relabel j) (ys 0) (![ right.relabel j,parameter.relabel j]) inpr tyr
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
 obtain ⟨el⟩ := eql
 obtain ⟨er⟩ := eqr
 exact ⟨InternalTagArithmeticSupportProof.trans el (InternalTagArithmeticSupportProof.symm er)⟩

theorem types4 (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter out lt rt : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 4) left parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 4) right parameter)))
 (hvl : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out left parameter)))
 (hvr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out right parameter)))
 (hyl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left lt left)))
 (hyr : Nonempty (Derivation body Delta (graph1 InternalUnpair.left rt right))) :
 Nonempty (Derivation body Delta (equal lt rt)) := by
 let q0 : Program 1 := rightOf (.projection 0)
 let q1 : Program 1 := leftOf q0
 let q2 : Program 1 := rightOf q0
 let q3 : Program 1 := leftOf q2
 let qs : Fin 4 → Program 1 := ![q0,q1,q2,q3]
 let xs : Fin 1 → OTerm alpha := ![out]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 have hx : (fun i => (xs i).relabel j) = (![out.relabel j] : Fin 1 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 let xx : Fin 1 → OTerm beta := ![out.relabel j]
 have h0 := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx (hq 0) (projectionValue 0 xx)
 have h1 := unaryRecover InternalUnpair.left q0 (ys 1) (ys 0) xx (hq 1) (hq 0)
 have h2 := unaryRecover InternalUnpair.right q0 (ys 2) (ys 0) xx (hq 2) (hq 0)
 have h3 := unaryRecover InternalUnpair.left q2 (ys 3) (ys 2) xx (hq 3) (hq 2)
 have hsl' := renameInto hsl j Theta hj
 have hsr' := renameInto hsr j Theta hj
 have htl' := renameInto htl j Theta hj
 have htr' := renameInto htr j Theta hj
 have hvl' := renameInto hvl j Theta hj
 have hvr' := renameInto hvr j Theta hj
 have hyl' := renameInto hyl j Theta hj
 have hyr' := renameInto hyr j Theta hj
 simp only [graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' htl' htr' hvl' hvr' hyl' hyr'
 have hbl := EvaluatorAlignmentBranchesProof.branch4 R (left.relabel j) (parameter.relabel j) (out.relabel j) htl' hvl'
 have hdl := rightComponent _ _ (left.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) h0 hbl
 have tyl := leftComponent _ _ (left.relabel j) (parameter.relabel j) (ys 0) (ys 1) h1 hdl
 have inpl := EvaluatorChildrenSelectorWiring.resultType body beta Theta (lt.relabel j) (left.relabel j) (parameter.relabel j) hyl'
 have eql := valueUnique OriginalRootObservation.resultType (lt.relabel j) (ys 1) (![ left.relabel j,parameter.relabel j]) inpl tyl
 have hbr := EvaluatorAlignmentBranchesProof.branch4 R (right.relabel j) (parameter.relabel j) (out.relabel j) htr' hvr'
 have hdr := rightComponent _ _ (right.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) h0 hbr
 have tyr := leftComponent _ _ (right.relabel j) (parameter.relabel j) (ys 0) (ys 1) h1 hdr
 have inpr := EvaluatorChildrenSelectorWiring.resultType body beta Theta (rt.relabel j) (right.relabel j) (parameter.relabel j) hyr'
 have eqr := valueUnique OriginalRootObservation.resultType (rt.relabel j) (ys 1) (![ right.relabel j,parameter.relabel j]) inpr tyr
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
 obtain ⟨el⟩ := eql
 obtain ⟨er⟩ := eqr
 exact ⟨InternalTagArithmeticSupportProof.trans el (InternalTagArithmeticSupportProof.symm er)⟩

theorem types5 (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter out lt rt : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 5) left parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 5) right parameter)))
 (hvl : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out left parameter)))
 (hvr : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) out right parameter)))
 (hyl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left lt left)))
 (hyr : Nonempty (Derivation body Delta (graph1 InternalUnpair.left rt right))) :
 Nonempty (Derivation body Delta (equal lt rt)) := by
 let q0 : Program 1 := rightOf (.projection 0)
 let q1 : Program 1 := leftOf q0
 let q2 : Program 1 := rightOf q0
 let q3 : Program 1 := leftOf q2
 let qs : Fin 4 → Program 1 := ![q0,q1,q2,q3]
 let xs : Fin 1 → OTerm alpha := ![out]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 have hx : (fun i => (xs i).relabel j) = (![out.relabel j] : Fin 1 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 let xx : Fin 1 → OTerm beta := ![out.relabel j]
 have h0 := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx (hq 0) (projectionValue 0 xx)
 have h1 := unaryRecover InternalUnpair.left q0 (ys 1) (ys 0) xx (hq 1) (hq 0)
 have h2 := unaryRecover InternalUnpair.right q0 (ys 2) (ys 0) xx (hq 2) (hq 0)
 have h3 := unaryRecover InternalUnpair.left q2 (ys 3) (ys 2) xx (hq 3) (hq 2)
 have hsl' := renameInto hsl j Theta hj
 have hsr' := renameInto hsr j Theta hj
 have htl' := renameInto htl j Theta hj
 have htr' := renameInto htr j Theta hj
 have hvl' := renameInto hvl j Theta hj
 have hvr' := renameInto hvr j Theta hj
 have hyl' := renameInto hyl j Theta hj
 have hyr' := renameInto hyr j Theta hj
 simp only [graph2Rename,graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' htl' htr' hvl' hvr' hyl' hyr'
 have hbl := EvaluatorAlignmentBranchesProof.branch5 R (left.relabel j) (parameter.relabel j) (out.relabel j) htl' hvl'
 have hdl := rightComponent _ _ (left.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) h0 hbl
 have restl := rightComponent _ _ (left.relabel j) (parameter.relabel j) (ys 0) (ys 2) h2 hdl
 have tyl := leftComponent _ _ (left.relabel j) (parameter.relabel j) (ys 2) (ys 3) h3 restl
 have inpl := EvaluatorChildrenSelectorWiring.resultType body beta Theta (lt.relabel j) (left.relabel j) (parameter.relabel j) hyl'
 have eql := valueUnique OriginalRootObservation.resultType (lt.relabel j) (ys 3) (![ left.relabel j,parameter.relabel j]) inpl tyl
 have hbr := EvaluatorAlignmentBranchesProof.branch5 R (right.relabel j) (parameter.relabel j) (out.relabel j) htr' hvr'
 have hdr := rightComponent _ _ (right.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) h0 hbr
 have restr := rightComponent _ _ (right.relabel j) (parameter.relabel j) (ys 0) (ys 2) h2 hdr
 have tyr := leftComponent _ _ (right.relabel j) (parameter.relabel j) (ys 2) (ys 3) h3 restr
 have inpr := EvaluatorChildrenSelectorWiring.resultType body beta Theta (rt.relabel j) (right.relabel j) (parameter.relabel j) hyr'
 have eqr := valueUnique OriginalRootObservation.resultType (rt.relabel j) (ys 3) (![ right.relabel j,parameter.relabel j]) inpr tyr
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
 obtain ⟨el⟩ := eql
 obtain ⟨er⟩ := eqr
 exact ⟨InternalTagArithmeticSupportProof.trans el (InternalTagArithmeticSupportProof.symm er)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTypesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTypesProof
