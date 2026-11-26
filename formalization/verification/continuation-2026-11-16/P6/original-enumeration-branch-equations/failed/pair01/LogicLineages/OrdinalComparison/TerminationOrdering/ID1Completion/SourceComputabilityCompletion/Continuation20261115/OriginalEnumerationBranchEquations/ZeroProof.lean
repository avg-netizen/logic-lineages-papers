module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationRecursionInterface.CombineScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.ZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm)
open OriginalEnumerationRecursionInterface
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem value (n : Nat) (node param vb : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node vb z))) :
    Nonempty (Derivation body Delta
      (graph2 (OriginalEnumerationRecursion.enumeration n) z node param)) := by
  have hr := SelectorProof.rankAt node param vb z hp
  have hd : Nonempty (Derivation body Delta (graph2 D z node param)) :=
    InternalAcceptanceBranchProof.zeroBranchIntro R (InternalAcceptance.constantZero 2)
      positiveDependencies z ![node,param] hr
      (InternalAcceptanceConjunctionProof.constantZeroValue ![node,param])
  have hm : Nonempty (Derivation body Delta
      (graph2 (OriginalEnumerationEquation.answerMap n) z z param)) :=
    InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 1)
      (OriginalEnumerationEquation.answerStep n) z (Fin.cons param Fin.elim0)
      (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons param Fin.elim0))
  have ha : Nonempty (Derivation body Delta
      (graph2 (OriginalEnumerationEquation.answers n) z node param)) :=
    binaryValue (OriginalEnumerationEquation.answerMap n) D (.projection 1)
      z z param ![node,param] hm hd (projectionValue 1 ![node,param])
  have hg := CombineScalarProof.zeroValue n node z param (SelectorProof.fuelAt node z param vb z hp)
  exact (OriginalEnumerationEquation.StatementChecks.exactEnumerationEquation n body alpha Delta
    node param z z ha).mpr hg

theorem internalZero : Targets.InternalZero := by
  intro n body alpha Delta node param vb out hp
  have hz := value n node param vb hp
  constructor
  · intro ho
    exact valueUnique (OriginalEnumerationRecursion.enumeration n) out z ![node,param] ho hz
  · rintro ⟨he⟩
    exact outputTransport (OriginalEnumerationRecursion.enumeration n) z out ![node,param]
      ⟨symm he⟩ hz
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.ZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationBranchEquations.ZeroProof
