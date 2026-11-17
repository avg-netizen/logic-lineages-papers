module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.FactsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.QueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Definitions FieldsSyntaxProof AllSyntaxProof SyntaxProof BindingProof FactsProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases)
def unary : Fin 2 → Program 2 :=
  ![pairOf (.projection 0) (.projection 1),pairOf (.projection 1) (.projection 0)]
def binary : Fin 4 → Program 4 :=
  ![pairOf (.projection 0) (.projection 2),pairOf (.projection 2) (.projection 0),
    pairOf (.projection 1) (.projection 3),pairOf (.projection 3) (.projection 1)]
theorem unaryRecover (left right : OTerm alpha) (ys : Fin 2 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (unary i) (ys i) ![left,right]))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 0) left right)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 1) right left)) :=
  ⟨InternalControlGraphSupportProof.binaryRecover _ (.projection 0) (.projection 1) _ _ _ _
    (hq 0) (projectionValue 0 _) (projectionValue 1 _),
   InternalControlGraphSupportProof.binaryRecover _ (.projection 1) (.projection 0) _ _ _ _
    (hq 1) (projectionValue 1 _) (projectionValue 0 _)⟩
theorem binaryRecover (a b c d : OTerm alpha) (ys : Fin 4 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (binary i) (ys i) ![a,b,c,d]))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 0) a c)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 1) c a)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 2) b d)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 3) d b)) :=
  ⟨InternalControlGraphSupportProof.binaryRecover _ (.projection 0) (.projection 2) _ _ _ _
    (hq 0) (projectionValue 0 _) (projectionValue 2 _),
   InternalControlGraphSupportProof.binaryRecover _ (.projection 2) (.projection 0) _ _ _ _
    (hq 1) (projectionValue 2 _) (projectionValue 0 _),
   InternalControlGraphSupportProof.binaryRecover _ (.projection 1) (.projection 3) _ _ _ _
    (hq 2) (projectionValue 1 _) (projectionValue 3 _),
   InternalControlGraphSupportProof.binaryRecover _ (.projection 3) (.projection 1) _ _ _ _
    (hq 3) (projectionValue 3 _) (projectionValue 1 _)⟩
theorem vector2Rename {beta : Type} (a b : OTerm alpha) (j : alpha → beta) :
    (fun i => (![a,b] i).relabel j) = ![a.relabel j,b.relabel j] := by
  funext i; fin_cases i <;> rfl
theorem vector4Rename {beta : Type} (a b c d : OTerm alpha) (j : alpha → beta) :
    (fun i => (![a,b,c,d] i).relabel j) = ![a.relabel j,b.relabel j,c.relabel j,d.relabel j] := by
  funext i; fin_cases i <;> rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.QueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.QueriesProof
