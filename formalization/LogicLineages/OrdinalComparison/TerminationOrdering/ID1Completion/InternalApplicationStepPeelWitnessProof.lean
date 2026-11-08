module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelCoreProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelCoreProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- These witness queries run on [domain,codomain,source,target,argument,step].
They use only the original total PR ASTs. They are eliminated from the result. -/
def fpQuery : Program 6 := rightOf (.projection 2)
def tpQuery : Program 6 := rightOf (.projection 3)
def apQuery : Program 6 := rightOf (.projection 4)
def pathQuery : Program 6 := leftOf (.projection 5)
def payloadQuery : Program 6 := rightOf (.projection 5)
def scQuery : Program 6 := pairOf fpQuery apQuery
def sbQuery : Program 6 := pairOf (.projection 0) scQuery
def snQuery : Program 6 := pairOf (two 6) sbQuery
def tcQuery : Program 6 := pairOf tpQuery apQuery
def tbQuery : Program 6 := pairOf (.projection 0) tcQuery
def tnQuery : Program 6 := pairOf (two 6) tbQuery
def prefixQuery : Program 6 := consOf (two 6) pathQuery
def sourceQuery : Program 6 := pairOf (.projection 1) snQuery
def targetQuery : Program 6 := pairOf (.projection 1) tnQuery
def stepQuery : Program 6 := pairOf prefixQuery payloadQuery

def witnessQueries : Fin 15 → Program 6 :=
  ![fpQuery,tpQuery,apQuery,pathQuery,payloadQuery,scQuery,sbQuery,snQuery,
    tcQuery,tbQuery,tnQuery,prefixQuery,sourceQuery,targetQuery,stepQuery]

theorem transitionFromQueries (endpoint : Program 5)
    (d e arrow s t a certificate k lifted : OTerm α) (ys : Fin 15 → OTerm α)
    (htag : Nonempty (Derivation body Gamma (taggedEdge d e arrow s t a certificate k)))
    (hend : Nonempty (Derivation body Gamma (graph5 endpoint (suc z) d e s t a)))
    (hlift : Nonempty (Derivation body Gamma (graph4 edgeLift lifted d e a certificate)))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (witnessQueries i) (ys i)
      (Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a (Fin.cons k Fin.elim0))))))))) :
    Nonempty (Derivation body Gamma (graph1 (transition endpoint) certificate lifted)) := by
  let xs : Fin 6 → OTerm α :=
    Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a (Fin.cons k Fin.elim0)))))
  apply transitionAtPairs endpoint d e arrow s t a certificate k lifted
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9)
    (ys 10) (ys 11) (ys 12) (ys 13) (ys 14) htag hend hlift
  · exact unaryRecover InternalUnpair.right (.projection 2) (ys 0) s xs (hq 0) (projectionValue 2 xs)
  · exact unaryRecover InternalUnpair.right (.projection 3) (ys 1) t xs (hq 1) (projectionValue 3 xs)
  · exact unaryRecover InternalUnpair.right (.projection 4) (ys 2) a xs (hq 2) (projectionValue 4 xs)
  · exact unaryRecover InternalUnpair.left (.projection 5) (ys 3) k xs (hq 3) (projectionValue 5 xs)
  · exact unaryRecover InternalUnpair.right (.projection 5) (ys 4) k xs (hq 4) (projectionValue 5 xs)
  · exact binaryRecover InternalPairing.pairing fpQuery apQuery (ys 5) (ys 0) (ys 2) xs
      (hq 5) (hq 0) (hq 2)
  · exact binaryRecover InternalPairing.pairing (.projection 0) scQuery (ys 6) d (ys 5) xs
      (hq 6) (projectionValue 0 xs) (hq 5)
  · exact binaryRecover InternalPairing.pairing (two 6) sbQuery (ys 7) positionTerm (ys 6) xs
      (hq 7) (twoValue xs) (hq 6)
  · exact binaryRecover InternalPairing.pairing tpQuery apQuery (ys 8) (ys 1) (ys 2) xs
      (hq 8) (hq 1) (hq 2)
  · exact binaryRecover InternalPairing.pairing (.projection 0) tcQuery (ys 9) d (ys 8) xs
      (hq 9) (projectionValue 0 xs) (hq 8)
  · exact binaryRecover InternalPairing.pairing (two 6) tbQuery (ys 10) positionTerm (ys 9) xs
      (hq 10) (twoValue xs) (hq 9)
  · exact binaryRecover InternalListCodec.consCode (two 6) pathQuery (ys 11) positionTerm (ys 3) xs
      (hq 11) (twoValue xs) (hq 3)
  · exact binaryRecover InternalPairing.pairing (.projection 1) snQuery (ys 12) e (ys 7) xs
      (hq 12) (projectionValue 1 xs) (hq 7)
  · exact binaryRecover InternalPairing.pairing (.projection 1) tnQuery (ys 13) e (ys 10) xs
      (hq 13) (projectionValue 1 xs) (hq 10)
  · exact binaryRecover InternalPairing.pairing prefixQuery payloadQuery (ys 14) (ys 11) (ys 4) xs
      (hq 14) (hq 11) (hq 4)

/-- No witness code survives as a new hypothesis. Original totality introduces
all finite witnesses, and the original calculus eliminates all of them. -/
theorem liftedValue (endpoint : Program 5)
    (d e arrow s t a certificate k lifted : OTerm α)
    (htag : Nonempty (Derivation body Gamma (taggedEdge d e arrow s t a certificate k)))
    (hend : Nonempty (Derivation body Gamma (graph5 endpoint (suc z) d e s t a)))
    (hlift : Nonempty (Derivation body Gamma (graph4 edgeLift lifted d e a certificate))) :
    Nonempty (Derivation body Gamma (graph1 (transition endpoint) certificate lifted)) := by
  apply queryCases witnessQueries
    (Fin.cons d (Fin.cons e (Fin.cons s (Fin.cons t (Fin.cons a (Fin.cons k Fin.elim0)))))) _
  intro β j ys Delta hj hq
  rw [graph1Rename]
  have htag' := renameInto htag j Delta hj
  have hend' := renameInto hend j Delta hj
  have hlift' := renameInto hlift j Delta hj
  simp only [taggedEdgeRename] at htag'
  simp only [graph5Rename,sucRelabel,zRelabel] at hend'
  simp only [graph4Rename] at hlift'
  simp only [consTermRename,emptyRename] at hq
  exact transitionFromQueries endpoint (d.relabel j) (e.relabel j) (arrow.relabel j)
    (s.relabel j) (t.relabel j) (a.relabel j) (certificate.relabel j) (k.relabel j)
    (lifted.relabel j) ys htag' hend' hlift' hq

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelWitnessProof
