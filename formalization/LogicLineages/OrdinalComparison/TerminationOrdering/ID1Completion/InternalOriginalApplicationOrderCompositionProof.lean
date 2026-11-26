module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderCompositionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalOriginalPairingOrderArithmeticProof InternalOriginalPairingOrderProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof InternalSquareRootArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A property of actual derivations, uniformly in the body, context and all
symbolic input/output terms. It is not a semantic monotonicity assertion. -/
def PreservesBounds {n : Nat} (p : Program n) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Gamma : List (Formula α))
    (xs ys : Fin n → OrdinaryArithmetic.Term α) (out other : OrdinaryArithmetic.Term α),
  (∀ i, Nonempty (Derivation body Gamma (ltF (xs i) (suc (ys i))))) →
  Nonempty (Derivation body Gamma (programGraph p out xs)) →
  Nonempty (Derivation body Gamma (programGraph p other ys)) →
  Nonempty (Derivation body Gamma (ltF out (suc other)))

theorem twoTuple {X : Type} (xs : Fin 2 → X) :
    Fin.cons (xs 0) (Fin.cons (xs 1) Fin.elim0) = xs := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i

theorem projectionBounds {n : Nat} (i : Fin n) : PreservesBounds (.projection i) := by
  intro body α Gamma xs ys out other hb hp hq
  exact weakTransport out other (xs i) (ys i)
    (valueUnique (.projection i) out (xs i) xs hp (projectionValue i xs))
    (valueUnique (.projection i) other (ys i) ys hq (projectionValue i ys)) (hb i)

theorem twoBounds (n : Nat) : PreservesBounds (two n) := by
  intro body α Gamma xs ys out other _ hp hq
  exact weakTransport out other positionTerm positionTerm
    (valueUnique (two n) out positionTerm xs hp (twoValue xs))
    (valueUnique (two n) other positionTerm ys hq (twoValue ys))
    ⟨equalToNext (refl positionTerm)⟩

/-- Composition eliminates the actual component graph witnesses twice, then
uses the proved internal pairing inequalities on those same witnesses. -/
theorem pairOfBounds {n : Nat} (p q : Program n)
    (hp : PreservesBounds p) (hq : PreservesBounds q) : PreservesBounds (pairOf p q) := by
  intro body α Gamma xs ys out other hb hx hy
  apply programCompositionCases InternalPairing.pairing ![p,q] out xs _ hx
  intro β j first Delta hj hfirst hcomponents
  simp only [orderRename,sucRelabel]
  have hy' := InternalGraphCompositionFunctionalityProof.renameInto hy j Delta hj
  rw [programRename] at hy'
  have hb' (i : Fin n) := InternalGraphCompositionFunctionalityProof.renameInto (hb i) j Delta hj
  simp only [orderRename,sucRelabel] at hb'
  apply programCompositionCases InternalPairing.pairing ![p,q]
    (other.relabel j) (fun i => (ys i).relabel j) _ hy'
  intro γ k second Theta hk hsecond hcomponents'
  simp only [orderRename,sucRelabel]
  have hfirst' := InternalGraphCompositionFunctionalityProof.renameInto hfirst k Theta hk
  rw [programRename] at hfirst'
  have hcomponents'' (i : Fin 2) := InternalGraphCompositionFunctionalityProof.renameInto (hcomponents i) k Theta hk
  simp only [programRename] at hcomponents''
  have hb'' (i : Fin n) := InternalGraphCompositionFunctionalityProof.renameInto (hb' i) k Theta hk
  simp only [orderRename,sucRelabel] at hb''
  have ha : Nonempty (Derivation body Theta
      (graph2 InternalPairing.pairing ((out.relabel j).relabel k)
        ((first 0).relabel k) ((first 1).relabel k))) := by
    change Nonempty (Derivation body Theta (programGraph InternalPairing.pairing _
      (Fin.cons ((first 0).relabel k) (Fin.cons ((first 1).relabel k) Fin.elim0))))
    rw [twoTuple (fun i => (first i).relabel k)]
    exact hfirst'
  have hc : Nonempty (Derivation body Theta
      (graph2 InternalPairing.pairing ((other.relabel j).relabel k) (second 0) (second 1))) := by
    change Nonempty (Derivation body Theta (programGraph InternalPairing.pairing _
      (Fin.cons (second 0) (Fin.cons (second 1) Fin.elim0))))
    rw [twoTuple second]
    exact hsecond
  exact bothWeak ((first 0).relabel k) (second 0) ((first 1).relabel k) (second 1)
    ((out.relabel j).relabel k) ((other.relabel j).relabel k) ha hc
    (hp body γ Theta (fun i => ((xs i).relabel j).relabel k)
      (fun i => ((ys i).relabel j).relabel k) ((first 0).relabel k) (second 0)
      hb'' (hcomponents'' 0) (hcomponents' 0))
    (hq body γ Theta (fun i => ((xs i).relabel j).relabel k)
      (fun i => ((ys i).relabel j).relabel k) ((first 1).relabel k) (second 1)
      hb'' (hcomponents'' 1) (hcomponents' 1))

/-- The literal nested original application constructor is monotone in all
four packed inputs; no fresh encoding or evaluated numeral is introduced. -/
theorem packedApplicationBounds : PreservesBounds packedApplication :=
  pairOfBounds (.projection 1)
    (pairOf (two 4) (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3))))
    (projectionBounds 1)
    (pairOfBounds (two 4) (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3)))
      (twoBounds 4)
      (pairOfBounds (.projection 0) (pairOf (.projection 2) (.projection 3))
        (projectionBounds 0)
        (pairOfBounds (.projection 2) (.projection 3) (projectionBounds 2) (projectionBounds 3))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderCompositionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderCompositionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderCompositionProof.packedApplicationBounds
