module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorHeadFiniteTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorHeadFiniteProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowSelectedProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorHeadWindowFiniteProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalCoverHeadWindowTargets (headArity headFittedWindow headKey)
open NumberedWindowInternalCoverHeadWindowSelectedProof (exact_OpenCoverHeadFittedWindow)
open NumberedWindowInternalConstructorHeadFiniteTargets (D)
open NumberedWindowInternalConstructorHeadFiniteProof (exact_OpenConstructorHeadFiniteCases)

private theorem sameListCode (xs : List Nat) : Encodable.encode xs = numbersNumber xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    rw [Encodable.encode_list_cons,Encodable.encode_nat,ih,numbersNumber,Nat.add_comm 1] <;> rfl

theorem exact_OpenOriginalSettingsHeadFiniteCases (s : Settings) (B : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (head : OTerm α) (goal : Formula α)
    (member : D B Γ (memberGraph (headsTerm s α) head))
    (next : ∀ n ∈ s.window.2, D B (eqn head (numeral n) :: Γ) goal) :
    D B Γ goal := by
  apply exact_OpenConstructorHeadFiniteCases s.window.2 B α Γ head goal _ next
  simpa only [headsTerm,sameListCode] using member

theorem exact_OpenOriginalFittedConstructorHeadFiniteCases
    (numbered : Bool) (s : Settings) (P : Program 2) (T : Program 1) (B : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx head result : OTerm α)
    (fields : List (OTerm α)) (goal : Formula α) (size : (head :: fields).length = headArity numbered)
    (admitted : D B Γ (windowGraph (headFittedWindow s P T) ctx result (headKey numbered head fields)))
    (next : ∀ n ∈ s.window.2, D B (eqn head (numeral n) :: Γ) goal) :
    D B Γ goal :=
  exact_OpenOriginalSettingsHeadFiniteCases s B α Γ head goal
    (exact_OpenCoverHeadFittedWindow numbered s P T B α Γ ctx head result fields size admitted) next

#print axioms exact_OpenOriginalSettingsHeadFiniteCases
#print axioms exact_OpenOriginalFittedConstructorHeadFiniteCases

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorHeadWindowFiniteProof
