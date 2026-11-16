module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.HeadInputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ParameterDeepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open InputProof ParameterTransportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem deepAt (xs : Fin 6 → OTerm alpha) (key answers param : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs))) :
    Nonempty (Derivation body Delta (graph3 labels (xs 4) key answers param ⊓ graph3 tupleBound (xs 5) key answers param)) := by
  apply queryCases ![innerQuery,middleQuery] xs _
  intro beta j ys Theta hj hq
  rw [conjunctionRename,graph3Rename,graph3Rename]
  have hi : Nonempty (Derivation body Theta (programGraph innerQuery (ys 0) (fun i => (xs i).relabel j))) := hq 0
  have hm : Nonempty (Derivation body Theta (programGraph middleQuery (ys 1) (fun i => (xs i).relabel j))) := hq 1
  have hpj := renameInto hp j Theta hj
  rw [programRename] at hpj
  have h1 := pairOfRight (.projection 2) middleQuery (param.relabel j) (ys 1) (fun i => (xs i).relabel j) hpj hm
  have h2 := pairOfRight (.projection 3) innerQuery (ys 1) (ys 0) (fun i => (xs i).relabel j) hm hi
  have hl := pairOfLeft (.projection 4) (.projection 5) (ys 0) ((xs 4).relabel j) (fun i => (xs i).relabel j)
    hi (projectionValue 4 (fun i : Fin 6 => (xs i).relabel j))
  have ht := pairOfRight (.projection 4) (.projection 5) (ys 0) ((xs 5).relabel j) (fun i => (xs i).relabel j)
    hi (projectionValue 5 (fun i : Fin 6 => (xs i).relabel j))
  have hm' := unaryValue InternalUnpair.right (.projection 2) (ys 1) (param.relabel j)
    ![key.relabel j,answers.relabel j,param.relabel j] h1 (projectionValue 2 ![key.relabel j,answers.relabel j,param.relabel j])
  have hi' := unaryValue InternalUnpair.right (rightOf (.projection 2)) (ys 0) (ys 1)
    ![key.relabel j,answers.relabel j,param.relabel j] h2 hm'
  exact andIntro
    (unaryValue InternalUnpair.left (rightOf (rightOf (.projection 2))) ((xs 4).relabel j) (ys 0)
      ![key.relabel j,answers.relabel j,param.relabel j] hl hi')
    (unaryValue InternalUnpair.right (rightOf (rightOf (.projection 2))) ((xs 5).relabel j) (ys 0)
      ![key.relabel j,answers.relabel j,param.relabel j] ht hi')

theorem labelsAt (xs : Fin 6 → OTerm alpha) (key answers param : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs))) :
    Nonempty (Derivation body Delta (graph3 labels (xs 4) key answers param)) := andLeft (deepAt xs key answers param hp)

theorem tupleBoundAt (xs : Fin 6 → OTerm alpha) (key answers param : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs))) :
    Nonempty (Derivation body Delta (graph3 tupleBound (xs 5) key answers param)) := andRight (deepAt xs key answers param hp)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ParameterDeepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ParameterDeepProof
