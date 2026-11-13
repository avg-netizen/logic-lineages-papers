module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaRootValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaRootProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (fieldsRename)
open OriginalLambdaTraversalInternalFieldsSyntaxProof (lambdaFieldsRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Original lambda root equality from actual constructor/type coordinates,
without redundant traversal-field hypotheses. Adapted from the accepted
OriginalHereditaryDeletionRowsLambdaRootEqualityProof value construction. -/
theorem sameChildValue (Q : Program 2) (input other domain codomain child otherChild parameter childParameter c gamma extended value out otherOut : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left codomain child)))
 (ht2 : Nonempty (Derivation body Delta (graph1 InternalUnpair.left codomain otherChild)))
 (hc : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input domain codomain child)))
 (hc2 : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor other domain codomain otherChild)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (he : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c extended)))
 (hv : Nonempty (Derivation body Delta (graph2 Q value child childParameter)))
 (hv2 : Nonempty (Derivation body Delta (graph2 Q value otherChild childParameter)))
 (ho : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) out input parameter)))
 (ho2 : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) otherOut other parameter)))
 :
 Nonempty (Derivation body Delta (equal out otherOut)) := by
 let a : Program 3 := .composition InternalListCodec.consCode ![.projection 0,.projection 1]
 let o : Program 3 := .composition InternalPairing.pairing ![.projection 1,.projection 2]
 let t : Program 3 := .composition InternalPairing.pairing ![.projection 1,o]
 let d : Program 3 := .composition InternalPairing.pairing ![.projection 0,t]
 let f : Program 3 := .composition InternalPairing.pairing ![InternalLessThan.constantOne 3,d]
 let qs : Fin 5 → Program 3 := ![a,o,t,d,f]
 let xs : Fin 3 → OTerm alpha := ![domain,codomain,value]
 apply queryCases qs xs _
 intro beta rho ys Theta hrho hq
 rw [OriginalTypedDecoderInternalLogicSyntaxProof.equalRename]
 let xx : Fin 3 → OTerm beta := ![domain.relabel rho,codomain.relabel rho,value.relabel rho]
 have hxx : (fun i => (xs i).relabel rho) = xx := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hxx] at hq
 have ha := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1) (ys 0) (domain.relabel rho) (codomain.relabel rho) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx)
 have hobs := binaryRecover InternalPairing.pairing (.projection 1) (.projection 2) (ys 1) (codomain.relabel rho) (value.relabel rho) xx (hq 1) (projectionValue 1 xx) (projectionValue 2 xx)
 have htyped := binaryRecover InternalPairing.pairing (.projection 1) o (ys 2) (codomain.relabel rho) (ys 1) xx (hq 2) (projectionValue 1 xx) (hq 1)
 have hdata := binaryRecover InternalPairing.pairing (.projection 0) t (ys 3) (domain.relabel rho) (ys 2) xx (hq 3) (projectionValue 0 xx) (hq 2)
 have hfinal := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 3) d (ys 4) (numeral 1) (ys 3) xx (hq 4) (InternalLessThanSupportProof.oneConstantValue xx) (hq 3)
 have htype := renameInto ht rho Theta hrho
 rw [graph1Rename] at htype
 have htype2 := renameInto ht2 rho Theta hrho
 rw [graph1Rename] at htype2
 have hc' := renameInto hc rho Theta hrho
 rw [graph3Rename] at hc'
 have hc2' := renameInto hc2 rho Theta hrho
 rw [graph3Rename] at hc2'
 have hp' := renameInto hp rho Theta hrho
 rw [graph2Rename] at hp'
 have he' := renameInto he rho Theta hrho
 rw [graph2Rename] at he'
 have hcp' := renameInto hcp rho Theta hrho
 rw [graph2Rename] at hcp'
 have hv' := renameInto hv rho Theta hrho
 rw [graph2Rename] at hv'
 have hv2' := renameInto hv2 rho Theta hrho
 rw [graph2Rename] at hv2'
 have ho' := renameInto ho rho Theta hrho
 rw [graph2Rename] at ho'
 have ho2' := renameInto ho2 rho Theta hrho
 rw [graph2Rename] at ho2'
 have hfields := OriginalLambdaConstructorGraphFieldsProof.constructorFields (input.relabel rho) (domain.relabel rho) (codomain.relabel rho) (child.relabel rho) (ys 0) hc' htype ha
 have root := OriginalHereditaryDeletionRowsLambdaRootValueProof.valueAtFields Q
  (input.relabel rho) (domain.relabel rho) (codomain.relabel rho) (child.relabel rho) (ys 0)
  (parameter.relabel rho) (childParameter.relabel rho) (c.relabel rho) (gamma.relabel rho) (extended.relabel rho) (value.relabel rho) (ys 1) (ys 2) (ys 3) (ys 4)
  hfields hp' he' hcp' hv' hobs htyped hdata hfinal
 have hfields2 := OriginalLambdaConstructorGraphFieldsProof.constructorFields (other.relabel rho) (domain.relabel rho) (codomain.relabel rho) (otherChild.relabel rho) (ys 0) hc2' htype2 ha
 have root2 := OriginalHereditaryDeletionRowsLambdaRootValueProof.valueAtFields Q
  (other.relabel rho) (domain.relabel rho) (codomain.relabel rho) (otherChild.relabel rho) (ys 0)
  (parameter.relabel rho) (childParameter.relabel rho) (c.relabel rho) (gamma.relabel rho) (extended.relabel rho) (value.relabel rho) (ys 1) (ys 2) (ys 3) (ys 4)
  hfields2 hp' he' hcp' hv2' hobs htyped hdata hfinal
 obtain ⟨eq1⟩ := valueUnique (OriginalRootObservation.rootObservation Q) (out.relabel rho) (ys 4) ![input.relabel rho,parameter.relabel rho] ho' root
 obtain ⟨eq2⟩ := valueUnique (OriginalRootObservation.rootObservation Q) (otherOut.relabel rho) (ys 4) ![other.relabel rho,parameter.relabel rho] ho2' root2
 simpa only [equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.trans eq1 (InternalTagArithmeticSupportProof.symm eq2)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaRootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaRootProof
