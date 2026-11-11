module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalHereditaryLambdaGlobal OriginalHereditaryLambda
open OriginalLambdaGuardLeafInternalProof (combine projectLeft projectRight)
open InternalAcceptanceConjunctionProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Remove the three literal conjunction wrappers at the SAME four inputs.
This is an original arithmetic graph inference, with no native calibration. -/
theorem wrapperFactor (endpoint : Program 6) (window : Program 1) (oldStep : Program 4)
    (source target certificate parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (accepted (wrapper endpoint window oldStep) source target certificate parameter))) :
    Nonempty (Derivation body Delta (accepted oldStep source target certificate parameter)) := by
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  let constructors := InternalAcceptance.conjunction
    (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest) OriginalConstructorLeaf.variableGuard
  have hc := conjunctionRecover
    (OriginalNeutralLeaf.refined endpoint window (OriginalSpineGuardLeaf.refined oldStep))
    constructors xs ha
  have hn := conjunctionRecover (OriginalSpineGuardLeaf.refined oldStep)
    (OriginalNeutralLeaf.leafGuard endpoint window) xs (projectLeft hc)
  have hs := conjunctionRecover oldStep (PositiveGuard.spineGuard BottomSpineMeasure.measure)
    xs (projectLeft hn)
  exact projectLeft hs

/-- Keep all three accepted original guards, replacing only the old factor
by a supplied accepted factor at those SAME inputs. In the closure proof
below, the guard supplier is the actual child's inner wrapper, not its parent. -/
theorem wrapperReplace (endpoint : Program 6) (window : Program 1) (oldStep newStep : Program 4)
    (source target certificate parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (accepted (wrapper endpoint window oldStep) source target certificate parameter)))
    (hb : Nonempty (Derivation body Delta (accepted newStep source target certificate parameter))) :
    Nonempty (Derivation body Delta
      (accepted (wrapper endpoint window newStep) source target certificate parameter)) := by
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  let constructors := InternalAcceptance.conjunction
    (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest) OriginalConstructorLeaf.variableGuard
  have hc := conjunctionRecover
    (OriginalNeutralLeaf.refined endpoint window (OriginalSpineGuardLeaf.refined oldStep))
    constructors xs ha
  have hn := conjunctionRecover (OriginalSpineGuardLeaf.refined oldStep)
    (OriginalNeutralLeaf.leafGuard endpoint window) xs (projectLeft hc)
  have hs := conjunctionRecover oldStep (PositiveGuard.spineGuard BottomSpineMeasure.measure)
    xs (projectLeft hn)
  exact conjunctionAccept
    (OriginalNeutralLeaf.refined endpoint window (OriginalSpineGuardLeaf.refined newStep))
    constructors xs
    (conjunctionAccept (OriginalSpineGuardLeaf.refined newStep)
      (OriginalNeutralLeaf.leafGuard endpoint window) xs
      (conjunctionAccept newStep (PositiveGuard.spineGuard BottomSpineMeasure.measure)
        xs hb (projectRight hs)) (projectRight hn)) (projectRight hc)

/-- Rebuild only the last graph in the original child bundle. The matching
and path tests, exact certificate-prefix graph and all four actual selector
graphs are passed through unchanged. -/
theorem childRecoveredReplace (oldStep newStep : Program 4)
    (source target certificate parameter sourceChild targetChild childStep childParam : OTerm alpha)
    (ha : Nonempty (Derivation body Delta
      (ChildRecovered oldStep source target certificate parameter
        sourceChild targetChild childStep childParam)))
    (hb : Nonempty (Derivation body Delta
      (accepted newStep sourceChild targetChild childStep childParam))) :
    Nonempty (Derivation body Delta
      (ChildRecovered newStep source target certificate parameter
        sourceChild targetChild childStep childParam)) := by
  have h1 := projectRight ha
  have h2 := projectRight h1
  have h3 := projectRight h2
  have h4 := projectRight h3
  have h5 := projectRight h4
  have h6 := projectRight h5
  exact combine (projectLeft ha) (combine (projectLeft h1) (combine (projectLeft h2)
    (combine (projectLeft h3) (combine (projectLeft h4) (combine (projectLeft h5)
      (combine (projectLeft h6) hb))))))

/-- The hereditary child supplies its whole inner wrapper at the SAME
actual child. Those guards rebuild the entire effective final leaf there.
No graph is inferred from equality of native evaluations. -/
theorem actualOriginalHereditaryLambdaGlobalInternalClosure :
    OriginalHereditaryLambdaGlobalTargets.ActualOriginalHereditaryLambdaGlobalInternalClosure := by
  intro endpoint window oldStep body alpha Delta source target certificate parameter psi ha k
  let inner := wrapper endpoint window oldStep
  let hereditary := OriginalHereditaryLambda.refined inner
  have hroot := wrapperFactor endpoint window hereditary source target certificate parameter
    (projectLeft ha)
  apply OriginalHereditaryLambdaChildProof.internalChildElimination inner
    body alpha Delta source target certificate parameter psi
    (combine hroot (projectRight ha))
  intro beta j Theta hj sourceChild targetChild childStep childParam hchild
  have h1 := projectRight hchild
  have h2 := projectRight h1
  have h3 := projectRight h2
  have h4 := projectRight h3
  have h5 := projectRight h4
  have h6 := projectRight h5
  have hhereditary := projectRight h6
  let ys : Fin 4 → OTerm beta :=
    Fin.cons sourceChild (Fin.cons targetChild (Fin.cons childStep (Fin.cons childParam Fin.elim0)))
  have hinner := projectLeft
    (conjunctionRecover inner (OriginalHereditaryLambda.guard inner) ys hhereditary)
  have hfinal := wrapperReplace endpoint window oldStep hereditary
    sourceChild targetChild childStep childParam hinner hhereditary
  exact k beta j Theta hj sourceChild targetChild childStep childParam
    (childRecoveredReplace hereditary (closedLeaf endpoint window oldStep)
      (source.relabel j) (target.relabel j) (certificate.relabel j) (parameter.relabel j)
      sourceChild targetChild childStep childParam hchild hfinal)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalInternalProof
