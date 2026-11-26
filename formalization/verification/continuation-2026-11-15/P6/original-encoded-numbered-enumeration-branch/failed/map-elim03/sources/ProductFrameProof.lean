module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.ProductsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.TupleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.ProductFrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalNumberedEnumerationBranch (product56 product456 product3456 product23456 product123456)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def queries : Fin 5 → Program 6 := ![product56,product456,product3456,product23456,product123456]
def facts (a b c d e f r56 r456 r3456 r23456 r123456 : OTerm alpha) : Formula alpha :=
  graph2 NumericDependencyCross.cross r56 e f ⊓
  graph2 NumericDependencyCross.cross r456 d r56 ⊓
  graph2 NumericDependencyCross.cross r3456 c r456 ⊓
  graph2 NumericDependencyCross.cross r23456 b r3456 ⊓
  graph2 NumericDependencyCross.cross r123456 a r23456

theorem recover (a b c d e f : OTerm alpha) (ys : Fin 5 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries i) (ys i) ![a,b,c,d,e,f]))) :
    Nonempty (Derivation body Delta (facts a b c d e f (ys 0) (ys 1) (ys 2) (ys 3) (ys 4))) := by
  let xs : Fin 6 → OTerm alpha := ![a,b,c,d,e,f]
  have h56 := binaryRecover NumericDependencyCross.cross (.projection 4) (.projection 5)
    (ys 0) e f xs (hq 0) (projectionValue 4 xs) (projectionValue 5 xs)
  have h456 := binaryRecover NumericDependencyCross.cross (.projection 3) product56
    (ys 1) d (ys 0) xs (hq 1) (projectionValue 3 xs) (hq 0)
  have h3456 := binaryRecover NumericDependencyCross.cross (.projection 2) product456
    (ys 2) c (ys 1) xs (hq 2) (projectionValue 2 xs) (hq 1)
  have h23456 := binaryRecover NumericDependencyCross.cross (.projection 1) product3456
    (ys 3) b (ys 2) xs (hq 3) (projectionValue 1 xs) (hq 2)
  have h123456 := binaryRecover NumericDependencyCross.cross (.projection 0) product23456
    (ys 4) a (ys 3) xs (hq 4) (projectionValue 0 xs) (hq 3)
  exact andIntro (andIntro (andIntro (andIntro h56 h456) h3456) h23456) h123456

theorem rawBranchRecover (a b c d e f out product : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph product123456 product ![a,b,c,d,e,f])))
    (hv : Nonempty (Derivation body Delta (programGraph OriginalNumberedEnumerationBranch.branch out ![a,b,c,d,e,f]))) :
    Nonempty (Derivation body Delta (graph1 (InternalListMap.map OriginalNumberedEnumerationBranch.tagPayload) out product)) :=
  unaryRecover (InternalListMap.map OriginalNumberedEnumerationBranch.tagPayload) product123456
    out product ![a,b,c,d,e,f] hv hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.ProductFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.ProductFrameProof
