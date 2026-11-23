module
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenFinishProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenReadProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveOutputTargets (args4 args5)
open NumberedWindowInternalSparsePositiveOutputWalkProof (succAt succAtValue)
open NumberedWindowInternalSparsePositiveOutputGuardProof (nonemptyCode recoverNonempty)
open NumberedWindowInternalParameterizedPositiveFold

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem argsRename {α β : Type} (c ty src cert dst : OTerm α) (j : α → β) :
    (fun i => (args5 c ty src cert dst i).relabel j) =
      args5 (c.relabel j) (ty.relabel j) (src.relabel j) (cert.relabel j) (dst.relabel j) := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun d =>
    Fin.cases ?_ (fun e => Fin.cases ?_ (fun u => Fin.elim0 u) e) d) b) a) i <;> rfl

private abbrev comparator (A : Program 4) : Program 5 :=
  .composition equalityTest ![walkAt A,succAt 4]

private theorem actualWalk (A : Program 4) (c ty src cert dst : OTerm α)
    (check : Nonempty (Derivation body Γ
      (programGraph (comparator A) (suc z) (args5 c ty src cert dst)))) :
    Nonempty (Derivation body Γ
      (programGraph (walkAt A) (suc dst) (args5 c ty src cert dst))) := by
  apply programCases (walkAt A) (args5 c ty src cert dst) _
  intro β j Δ current keep held
  rw [programRename,argsRename,sucRelabel]
  rw [argsRename] at held
  have check' := renameInto check j Δ keep
  rw [programRename,argsRename,sucRelabel,zRelabel] at check'
  let tape := args5 (c.relabel j) (ty.relabel j) (src.relabel j) (cert.relabel j) (dst.relabel j)
  let output := suc (dst.relabel j)
  let slots : Fin 2 → OTerm β := Fin.cons current (Fin.cons output Fin.elim0)
  have haveCompare := compositionRecover equalityTest ![walkAt A,succAt 4] (suc z) tape slots check' (fun i =>
    Fin.cases held (Fin.cases (succAtValue (4 : Fin 5) tape) (fun u => Fin.elim0 u)) i)
  have aligned := equalityOfAcceptance current output haveCompare
  exact outputTransport (walkAt A) current output tape aligned held

private theorem actualFinish (A : Program 4) (c ty src cert dst : OTerm α)
    (held : Nonempty (Derivation body Γ
      (programGraph (walkAt A) (suc dst) (args5 c ty src cert dst)))) :
    Nonempty (Derivation body Γ
      (programGraph (finishAt A) (suc dst) (args4 c ty (suc src) cert))) := by
  let xs := args5 c ty src cert dst
  apply compositionRecover (finishAt A) NumberedWindowInternalSparsePositiveOutputWalkProof.picks
    (suc dst) xs (args4 c ty (suc src) cert) held
  intro i
  exact Fin.cases (projectionValue (0 : Fin 5) xs)
    (Fin.cases (projectionValue (1 : Fin 5) xs)
      (Fin.cases (succAtValue (2 : Fin 5) xs) (Fin.cases (projectionValue (3 : Fin 5) xs)
        (fun u => Fin.elim0 u)))) i

/-- An actual open acceptance is nonempty and its actual finish
returns exactly the successful requested optional output. -/
theorem exact_OpenParameterizedPositiveToFinish (A : Program 4) (c ty src cert dst : OTerm α)
    (held : Nonempty (Derivation body Γ
      (programGraph (positiveAt A) (suc z) (args5 c ty src cert dst)))) :
    Nonempty (Derivation body Γ ((eqn cert z).not ⊓
      programGraph (finishAt A) (suc dst) (args4 c ty (suc src) cert))) := by
  obtain ⟨both⟩ := conjunctionRecover nonemptyCode (comparator A) (args5 c ty src cert dst) held
  obtain ⟨nonemptyProof⟩ := recoverNonempty c ty src cert dst ⟨Derivation.conjunctionLeft both⟩
  obtain ⟨out⟩ := actualFinish A c ty src cert dst
    (actualWalk A c ty src cert dst ⟨Derivation.conjunctionRight both⟩)
  exact ⟨Derivation.conjunctionIntroduction nonemptyProof out⟩

#print axioms exact_OpenParameterizedPositiveToFinish
end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedPositiveFoldOpenReadProof
