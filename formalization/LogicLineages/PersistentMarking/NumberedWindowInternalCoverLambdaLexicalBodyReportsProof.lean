module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBodyReportsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue valueUnique)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafTypeTest)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (grammarTypeAt)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary)
open NumberedWindowInternalChosenAuxMeasureCombine (callOne)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaLexicalShapeProof (actualLambdaLexicalShape)
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (liftRawReport)
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem oneValue (P : Program 1) (Q : Program 2) (out v : OTerm α) (xs : Fin 2 → OTerm α)
    (code : Nonempty (Derivation body Γ (unary P out v)))
    (arg : Nonempty (Derivation body Γ (programGraph Q v xs))) :
    Nonempty (Derivation body Γ (programGraph (callOne P Q) out xs)) := by
  apply compositionValue P (fun _ : Fin 1 => Q) out xs ![v] code
  intro i
  obtain rfl := Fin.eq_zero i
  exact arg

private theorem twoValue (P a b : Program 2) (out x y : OTerm α) (xs : Fin 2 → OTerm α)
    (code : Nonempty (Derivation body Γ (programGraph P out ![x,y])))
    (ax : Nonempty (Derivation body Γ (programGraph a x xs)))
    (by' : Nonempty (Derivation body Γ (programGraph b y xs))) :
    Nonempty (Derivation body Γ (programGraph (binary P a b) out xs)) := by
  apply compositionValue P (Fin.cons a (Fin.cons b Fin.elim0)) out xs ![x,y] code
  intro i
  exact Fin.cases ax (Fin.cases by' (fun j => Fin.elim0 j)) i

theorem actualLambdaDomainK (s : Settings) (ctx ty q : OTerm α)
    (seen : Nonempty (Derivation body Γ
      (programGraph (onRaw (leafTypeTest s)) (suc z) ![ctx,lambdaTerm ty q]))) :
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) := by
  let raw := lambdaTerm ty q
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  have shape := actualLambdaLexicalShape (body := body) (Γ := Γ) ty q
  have test : Nonempty (Derivation body Γ (unary (leafTypeTest s) (suc z) raw)) := by
    apply compositionRecover (leafTypeTest s) (fun _ : Fin 1 => Program.projection 1)
      (suc z) xs ![raw] seen
    intro j
    obtain rfl := Fin.eq_zero j
    exact projectionValue 1 xs
  have fit : Nonempty (Derivation body Γ (unary (grammarTypeAt s) (suc z) ty)) := by
    apply compositionRecover (grammarTypeAt s) (fun _ : Fin 1 => field 0) (suc z) ![raw] ![ty] test
    intro j
    obtain rfl := Fin.eq_zero j
    exact shape.domainRead
  let code := Encodable.encode s.types
  apply compositionRecover scratchMember ![literal 1 code,.projection 0] (suc z) ![ty] ![numeral code,ty] fit
  intro j
  exact Fin.cases (literalGraph code ![ty])
    (Fin.cases (projectionValue 0 ![ty]) (fun k => Fin.elim0 k)) j

theorem recoverPrecedingLambdaChild (s : Settings) (B : Program 2) (T : Program 1)
    (ctx ty q res childTy : OTerm α)
    (domain : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)))
    (child : Nonempty (Derivation body Γ
      (programGraph (lambdaOldBody s B T) (suc childTy) ![ctx,lambdaTerm ty q])))
    (returned : Nonempty (Derivation body Γ
      (programGraph (lambdaLexicalResult s B T) (suc res) ![ctx,lambdaTerm ty q]))) :
    ActualPrecedingLambdaChild s B T body Γ ctx ty q res childTy := by
  let raw := lambdaTerm ty q
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let pushed := rawCons ty ctx
  let F := precedingIntrinsic s B T
  have shape := actualLambdaLexicalShape (body := body) (Γ := Γ) ty q
  have tyAt := liftRawReport (field 0) ctx raw ty shape.domainRead
  have qAt := liftRawReport (field 1) ctx raw q shape.childRead
  have push : Nonempty (Derivation body Γ (programGraph lambdaLexicalPush pushed xs)) :=
    twoValue fieldCons (onRaw (field 0)) (.projection 0) pushed ty ctx xs (consGraph ty ctx) tyAt (projectionValue 0 xs)
  have oldChild : Nonempty (Derivation body Γ (programGraph F (suc childTy) ![pushed,q])) := by
    apply compositionRecover F (Fin.cons lambdaLexicalPush (Fin.cons (onRaw (field 1)) Fin.elim0))
      (suc childTy) xs ![pushed,q] child
    intro j
    exact Fin.cases push (Fin.cases qAt (fun k => Fin.elim0 k)) j
  have observed := (exact_OpenIntrinsicQuery F body α Γ pushed childTy q).mpr oldChild
  have lowered := oneValue predecessor (lambdaOldBody s B T) childTy (suc childTy) xs
    (predecessorSuccessor childTy) child
  let arrow := rawCons ty childTy
  have arrowReport : Nonempty (Derivation body Γ (programGraph (lambdaArrowCode s B T) arrow xs)) :=
    twoValue fieldCons (onRaw (field 0)) (callOne predecessor (lambdaOldBody s B T)) arrow ty childTy xs
      (consGraph ty childTy) tyAt lowered
  have sameCode := oneValue .succ (lambdaArrowCode s B T) (suc arrow) arrow xs
    (successorValue ![arrow]) arrowReport
  obtain ⟨equal⟩ := valueUnique (lambdaLexicalResult s B T) (suc res) (suc arrow) xs returned sameCode
  exact ⟨observed,domain,⟨cancelSuc equal⟩⟩

#print axioms actualLambdaDomainK
#print axioms recoverPrecedingLambdaChild

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBodyReportsProof
