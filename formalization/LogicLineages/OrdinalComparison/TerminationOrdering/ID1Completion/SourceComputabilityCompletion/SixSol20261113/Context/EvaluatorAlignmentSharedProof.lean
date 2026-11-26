module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenInverseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentSharedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorChildrenInverseProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
open SixSol20261113.Erasure.EvaluatorErasureSyntax

theorem application (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter out ld lc rd rc : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hvl : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out left parameter)))
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) left parameter)))
 (hdl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain ld left parameter)))
 (hcl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.resultType lc left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (hvr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out right parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) right parameter)))
 (hdr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain rd right parameter)))
 (hcr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.resultType rc right parameter))) :
 Nonempty (Derivation body Delta (equal ld rd ⊓ equal lc rc)) := by
 let q0 : Program 1 := rightOf (.projection 0)
 let q1 : Program 1 := leftOf q0
 let q2 : Program 1 := rightOf q1
 let q3 : Program 1 := leftOf q2
 let q4 : Program 1 := rightOf q2
 let q5 : Program 1 := leftOf q4
 let qs : Fin 6 → Program 1 := ![q0,q1,q2,q3,q4,q5]
 let xs : Fin 1 → OTerm alpha := ![out]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 let xx : Fin 1 → OTerm beta := ![out.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 have h0 := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx (hq 0) (projectionValue 0 xx)
 have h1 := unaryRecover InternalUnpair.left q0 (ys 1) (ys 0) xx (hq 1) (hq 0)
 have h2 := unaryRecover InternalUnpair.right q1 (ys 2) (ys 1) xx (hq 2) (hq 1)
 have h3 := unaryRecover InternalUnpair.left q2 (ys 3) (ys 2) xx (hq 3) (hq 2)
 have h4 := unaryRecover InternalUnpair.right q2 (ys 4) (ys 2) xx (hq 4) (hq 2)
 have h5 := unaryRecover InternalUnpair.left q4 (ys 5) (ys 4) xx (hq 5) (hq 4)
 have hsl' := renameInto hsl j Theta hj
 have hvl' := renameInto hvl j Theta hj
 have htl' := renameInto htl j Theta hj
 have hdl' := renameInto hdl j Theta hj
 have hcl' := renameInto hcl j Theta hj
 have hsr' := renameInto hsr j Theta hj
 have hvr' := renameInto hvr j Theta hj
 have htr' := renameInto htr j Theta hj
 have hdr' := renameInto hdr j Theta hj
 have hcr' := renameInto hcr j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hvl' htl' hdl' hcl' hsr' hvr' htr' hdr' hcr'
 have rootl := EvaluatorChildrenProjectionProof.recursiveRoot R H G M W (left.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) (ys 1) hsl' hvl' h0 h1
 have fieldsl := EvaluatorAlignmentFieldsProof.applicationAt (OriginalHereditaryEvaluatorDefinitions.evaluator R)
   (left.relabel j) (parameter.relabel j) (ys 1) (ys 2) (ys 4) (ys 3) (ys 5) htl' rootl h2 h3 h4 h5
 have edl := valueUnique OriginalRootObservation.domain (ld.relabel j) (ys 3)
   (![left.relabel j,parameter.relabel j]) hdl' (andLeft fieldsl)
 have ecl := valueUnique OriginalRootObservation.resultType (lc.relabel j) (ys 5)
   (![left.relabel j,parameter.relabel j]) hcl' (andRight fieldsl)
 have rootr := EvaluatorChildrenProjectionProof.recursiveRoot R H G M W (right.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) (ys 1) hsr' hvr' h0 h1
 have fieldsr := EvaluatorAlignmentFieldsProof.applicationAt (OriginalHereditaryEvaluatorDefinitions.evaluator R)
   (right.relabel j) (parameter.relabel j) (ys 1) (ys 2) (ys 4) (ys 3) (ys 5) htr' rootr h2 h3 h4 h5
 have edr := valueUnique OriginalRootObservation.domain (rd.relabel j) (ys 3)
   (![right.relabel j,parameter.relabel j]) hdr' (andLeft fieldsr)
 have ecr := valueUnique OriginalRootObservation.resultType (rc.relabel j) (ys 5)
   (![right.relabel j,parameter.relabel j]) hcr' (andRight fieldsr)
 simp only [conjunctionRename,equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
 obtain ⟨edl⟩ := edl
 obtain ⟨edr⟩ := edr
 obtain ⟨ecl⟩ := ecl
 obtain ⟨ecr⟩ := ecr
 exact andIntro ⟨InternalTagArithmeticSupportProof.trans edl (InternalTagArithmeticSupportProof.symm edr)⟩
   ⟨InternalTagArithmeticSupportProof.trans ecl (InternalTagArithmeticSupportProof.symm ecr)⟩

theorem lambda (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter out ld lc rd rc : OTerm alpha)
 (hsl : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hvl : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out left parameter)))
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) left parameter)))
 (hdl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain ld left parameter)))
 (hcl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.codomain lc left parameter)))
 (hsr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (hvr : Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) out right parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) right parameter)))
 (hdr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain rd right parameter)))
 (hcr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.codomain rc right parameter))) :
 Nonempty (Derivation body Delta (equal ld rd ⊓ equal lc rc)) := by
 let q0 : Program 1 := rightOf (.projection 0)
 let q1 : Program 1 := leftOf q0
 let q2 : Program 1 := rightOf q1
 let q3 : Program 1 := leftOf q2
 let q4 : Program 1 := rightOf q2
 let q5 : Program 1 := leftOf q4
 let qs : Fin 6 → Program 1 := ![q0,q1,q2,q3,q4,q5]
 let xs : Fin 1 → OTerm alpha := ![out]
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hq
 let xx : Fin 1 → OTerm beta := ![out.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 have h0 := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (out.relabel j) xx (hq 0) (projectionValue 0 xx)
 have h1 := unaryRecover InternalUnpair.left q0 (ys 1) (ys 0) xx (hq 1) (hq 0)
 have h2 := unaryRecover InternalUnpair.right q1 (ys 2) (ys 1) xx (hq 2) (hq 1)
 have h3 := unaryRecover InternalUnpair.left q2 (ys 3) (ys 2) xx (hq 3) (hq 2)
 have h4 := unaryRecover InternalUnpair.right q2 (ys 4) (ys 2) xx (hq 4) (hq 2)
 have h5 := unaryRecover InternalUnpair.left q4 (ys 5) (ys 4) xx (hq 5) (hq 4)
 have hsl' := renameInto hsl j Theta hj
 have hvl' := renameInto hvl j Theta hj
 have htl' := renameInto htl j Theta hj
 have hdl' := renameInto hdl j Theta hj
 have hcl' := renameInto hcl j Theta hj
 have hsr' := renameInto hsr j Theta hj
 have hvr' := renameInto hvr j Theta hj
 have htr' := renameInto htr j Theta hj
 have hdr' := renameInto hdr j Theta hj
 have hcr' := renameInto hcr j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hvl' htl' hdl' hcl' hsr' hvr' htr' hdr' hcr'
 have rootl := EvaluatorChildrenProjectionProof.recursiveRoot R H G M W (left.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) (ys 1) hsl' hvl' h0 h1
 have fieldsl := EvaluatorAlignmentFieldsProof.lambdaAt (OriginalHereditaryEvaluatorDefinitions.evaluator R)
   (left.relabel j) (parameter.relabel j) (ys 1) (ys 2) (ys 4) (ys 3) (ys 5) htl' rootl h2 h3 h4 h5
 have edl := valueUnique OriginalRootObservation.domain (ld.relabel j) (ys 3)
   (![left.relabel j,parameter.relabel j]) hdl' (andLeft fieldsl)
 have ecl := valueUnique OriginalRootObservation.codomain (lc.relabel j) (ys 5)
   (![left.relabel j,parameter.relabel j]) hcl' (andRight fieldsl)
 have rootr := EvaluatorChildrenProjectionProof.recursiveRoot R H G M W (right.relabel j) (parameter.relabel j) (out.relabel j) (ys 0) (ys 1) hsr' hvr' h0 h1
 have fieldsr := EvaluatorAlignmentFieldsProof.lambdaAt (OriginalHereditaryEvaluatorDefinitions.evaluator R)
   (right.relabel j) (parameter.relabel j) (ys 1) (ys 2) (ys 4) (ys 3) (ys 5) htr' rootr h2 h3 h4 h5
 have edr := valueUnique OriginalRootObservation.domain (rd.relabel j) (ys 3)
   (![right.relabel j,parameter.relabel j]) hdr' (andLeft fieldsr)
 have ecr := valueUnique OriginalRootObservation.codomain (rc.relabel j) (ys 5)
   (![right.relabel j,parameter.relabel j]) hcr' (andRight fieldsr)
 simp only [conjunctionRename,equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel]
 obtain ⟨edl⟩ := edl
 obtain ⟨edr⟩ := edr
 obtain ⟨ecl⟩ := ecl
 obtain ⟨ecr⟩ := ecr
 exact andIntro ⟨InternalTagArithmeticSupportProof.trans edl (InternalTagArithmeticSupportProof.symm edr)⟩
   ⟨InternalTagArithmeticSupportProof.trans ecl (InternalTagArithmeticSupportProof.symm ecr)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentSharedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentSharedProof
