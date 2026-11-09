module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z suc)
open UniformCertificateCompletion.PositiveGuard
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact INTERNAL meaning of L1's literal shared guard at actual supplied
measure/depth graphs. This is independent of any numerical calibration of
the bottom, measure or edge Programs. The arbitrary source flag need not be
Boolean: the original exact-one normalization implements the implication. -/
def ActualPositiveGuardEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (bottom measure : Program 1) (edge : Program 4)
    (α : Type) (Delta : List (Formula α))
    (x y certificate parameter sourceMark targetMark sourceDepth targetDepth : OTerm α),
  Nonempty (Derivation body Delta
    ((graph1 measure sourceMark x ⊓
      (graph1 measure targetMark y ⊓
        (graph1 InternalUnpair.right sourceDepth sourceMark ⊓
          graph1 InternalUnpair.right targetDepth targetMark))).imp
      ((accepted bottom measure edge x y certificate parameter).iff
        ((graph4 (InternalParameterizedPathChecker.checker edge true)
            (suc z) x y certificate parameter) ⊓
          ((graph1 bottom (suc z) x).not ⊓
            ((graph1 InternalUnpair.left (suc z) sourceMark).imp
              (graph1 InternalUnpair.left (suc z) targetMark ⊓
                arithmeticEmbedding.onFormula
                  (OrdinaryArithmetic.lessFormula targetDepth sourceDepth))))))))

/-- The actual checker, without measure witnesses or shape assumptions,
already rejects a supplied exact bottom source. -/
def ActualPositiveGuardNonBottom : Prop :=
  ∀ (body : Positive (Fin 1)) (bottom measure : Program 1) (edge : Program 4)
    (α : Type) (Delta : List (Formula α)) (x y certificate parameter : OTerm α),
  Nonempty (Derivation body Delta
    ((accepted bottom measure edge x y certificate parameter).imp
      (graph1 bottom (suc z) x).not))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesTargets
