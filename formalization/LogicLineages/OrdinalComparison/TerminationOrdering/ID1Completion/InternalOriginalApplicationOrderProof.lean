module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderCompositionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof InternalGraphCompositionTotalityProof
open InternalRecursionGraphStepSyntaxProof InternalRecursionClosureProof
open InternalOriginalPairingOrderArithmeticProof InternalOriginalPairingOrderProof
open InternalOriginalApplicationOrderCompositionProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Equal original left fields let the original pair order reflect to the
supplied right fields. These are actual unpair/reconstruction graphs. -/
theorem payloadBound (typeCode x y xp yp : OrdinaryArithmetic.Term α)
    (hx : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typeCode x)))
    (hy : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left typeCode y)))
    (hxp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right xp x)))
    (hyp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right yp y)))
    (hb : Nonempty (Derivation body Gamma (ltF x (suc y)))) :
    Nonempty (Derivation body Gamma (ltF xp (suc yp))) :=
  rightReflect typeCode xp yp x y
    (reconstructPair x typeCode xp hx hxp) (reconstructPair y typeCode yp hy hyp) hb

/-- The fresh right-field witnesses are kept distinct from one another and
from the input type coordinates throughout the original constructor assembly. -/
theorem applicationAtPayloads (ar d e f a f' a' fp ap fp' ap' parent parent' : OrdinaryArithmetic.Term α)
    (hf : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left ar f)))
    (hf' : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left ar f')))
    (ha : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (ha' : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a')))
    (hfp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (hfp' : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp' f')))
    (hap : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    (hap' : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap' a')))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hp' : Nonempty (Derivation body Gamma (graph4 application parent' d e f' a')))
    (hfb : Nonempty (Derivation body Gamma (ltF f' (suc f))))
    (hab : Nonempty (Derivation body Gamma (ltF a' (suc a)))) :
    Nonempty (Derivation body Gamma (ltF parent' (suc parent))) := by
  apply packedApplicationBounds body α Gamma
    (Fin.cons d (Fin.cons e (Fin.cons fp' (Fin.cons ap' Fin.elim0))))
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))) parent' parent
  · intro i
    exact Fin.cases ⟨equalToNext (refl d)⟩
      (Fin.cases ⟨equalToNext (refl e)⟩
        (Fin.cases (payloadBound ar f' f fp' fp hf' hf hfp' hfp hfb)
          (Fin.cases (payloadBound d a' a ap' ap ha' ha hap' hap hab)
            (fun k => Fin.elim0 k)))) i
  · exact applicationForward d e f' a' fp' ap' parent' hfp' hap' hp'
  · exact applicationForward d e f a fp ap parent hfp hap hp

/-- All four original right-field values come from the existing internal
Program-totality theorem. No natural-number valuation is selected. -/
theorem applicationBound (ar d e f a f' a' parent parent' : OrdinaryArithmetic.Term α)
    (hf : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left ar f)))
    (hf' : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left ar f')))
    (ha : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (ha' : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a')))
    (hp : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hp' : Nonempty (Derivation body Gamma (graph4 application parent' d e f' a')))
    (hfb : Nonempty (Derivation body Gamma (ltF f' (suc f))))
    (hab : Nonempty (Derivation body Gamma (ltF a' (suc a)))) :
    Nonempty (Derivation body Gamma (ltF parent' (suc parent))) := by
  let inputs : Fin 4 → OrdinaryArithmetic.Term α := Fin.cons f (Fin.cons a (Fin.cons f' (Fin.cons a' Fin.elim0)))
  apply supplyOutputs body 4 4
    (fun i => OrdinaryArithmetic.graphFormula (rightOf (.projection i)))
    (fun i => (actualOriginalPrograms body 4 (rightOf (.projection i))).1)
    α Gamma inputs _
  intro β j Delta payloads hj hs
  simp only [orderRename,sucRelabel]
  let renamed : Fin 4 → OrdinaryArithmetic.Term β := fun i => (inputs i).relabel j
  have values (i : Fin 4) : Nonempty (Derivation body Delta
      (graph1 InternalUnpair.right (payloads i) (renamed i))) :=
    unaryRecover InternalUnpair.right (.projection i) (payloads i) (renamed i) renamed
      (hs i) (projectionValue i renamed)
  have hf1 := InternalGraphCompositionFunctionalityProof.renameInto hf j Delta hj
  have hf2 := InternalGraphCompositionFunctionalityProof.renameInto hf' j Delta hj
  have ha1 := InternalGraphCompositionFunctionalityProof.renameInto ha j Delta hj
  have ha2 := InternalGraphCompositionFunctionalityProof.renameInto ha' j Delta hj
  rw [graph1Rename] at hf1 hf2 ha1 ha2
  have hp1 := InternalGraphCompositionFunctionalityProof.renameInto hp j Delta hj
  have hp2 := InternalGraphCompositionFunctionalityProof.renameInto hp' j Delta hj
  rw [graph4Rename] at hp1 hp2
  have hfb' := InternalGraphCompositionFunctionalityProof.renameInto hfb j Delta hj
  have hab' := InternalGraphCompositionFunctionalityProof.renameInto hab j Delta hj
  simp only [orderRename,sucRelabel] at hfb' hab'
  exact applicationAtPayloads (ar.relabel j) (d.relabel j) (e.relabel j)
    (f.relabel j) (a.relabel j) (f'.relabel j) (a'.relabel j)
    (payloads 0) (payloads 1) (payloads 2) (payloads 3)
    (parent.relabel j) (parent'.relabel j) hf1 hf2 ha1 ha2
    (values 0) (values 2) (values 1) (values 3) hp1 hp2 hfb' hab'

theorem actualOriginalApplicationCodeMonotonicity :
    InternalOriginalApplicationOrderTargets.ActualOriginalApplicationCodeMonotonicity := by
  intro body α Delta arrow domain codomain function argument function' argument' parent parent'
  let premise := graph2 InternalListCodec.consCode arrow domain codomain ⊓
    (graph1 InternalUnpair.left arrow function ⊓
      (graph1 InternalUnpair.left arrow function' ⊓
        (graph1 InternalUnpair.left domain argument ⊓
          (graph1 InternalUnpair.left domain argument' ⊓
            (graph4 application parent domain codomain function argument ⊓
              (graph4 application parent' domain codomain function' argument' ⊓
                (InternalParameterizedBoundedDescentNormalizer.atMost function' function ⊓
                  InternalParameterizedBoundedDescentNormalizer.atMost argument' argument)))))))
  have h : Derivation body (premise :: Delta) premise := Derivation.hypothesis List.mem_cons_self
  -- The exact target's arrow cons graph remains in the antecedent. The bound
  -- itself requires only its common left-field witnesses, so that conjunct is
  -- retained without being strengthened or replaced.
  have h1 := Derivation.conjunctionRight h
  have h2 := Derivation.conjunctionRight h1
  have h3 := Derivation.conjunctionRight h2
  have h4 := Derivation.conjunctionRight h3
  have h5 := Derivation.conjunctionRight h4
  have h6 := Derivation.conjunctionRight h5
  have h7 := Derivation.conjunctionRight h6
  obtain ⟨result⟩ := applicationBound arrow domain codomain function argument function' argument' parent parent'
    ⟨Derivation.conjunctionLeft h1⟩ ⟨Derivation.conjunctionLeft h2⟩
    ⟨Derivation.conjunctionLeft h3⟩ ⟨Derivation.conjunctionLeft h4⟩
    ⟨Derivation.conjunctionLeft h5⟩ ⟨Derivation.conjunctionLeft h6⟩
    ⟨Derivation.conjunctionLeft h7⟩ ⟨Derivation.conjunctionRight h7⟩
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderProof.actualOriginalApplicationCodeMonotonicity
