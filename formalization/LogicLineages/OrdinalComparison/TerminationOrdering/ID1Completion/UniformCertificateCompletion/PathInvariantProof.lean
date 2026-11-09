module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.TypingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTypedEdgePresentationSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathInvariantProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open UniformCertificateCompletion.Path UniformCertificateCompletion.PathSupportProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceSupportProof
open InternalGraphCompositionEqualityProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem invariantRecover (context : Nat) (data : Data) (sigma tau : Ty)
    (parameter domain codomain argument value : OTerm α)
    (h : Nonempty (Derivation body Delta
      (programGraph (invariant context data sigma tau) (suc z)
        (arguments parameter domain codomain argument value)))) :
    Nonempty (Derivation body Delta
      (invariantFactors context data sigma tau parameter domain codomain argument value)) := by
  let xs := arguments parameter domain codomain argument value
  have h0 := conjunctionRecover _ _ xs h
  have h1 := conjunctionRecover _ _ xs (andRight h0)
  have h2 := conjunctionRecover _ _ xs (andRight h1)
  have h3 := conjunctionRecover _ _ xs (andRight h2)
  have hx := typedRecover data (.projection 4) (Path.constant 5 (typeNumber (.arrow sigma tau)))
    (.projection 0) value (numeral (typeNumber (.arrow sigma tau))) parameter xs
    (projectionValue 4 xs) (constantValue 5 (typeNumber (.arrow sigma tau)) xs)
    (projectionValue 0 xs) (andLeft h3)
  have ha := typedRecover data (.projection 3) (Path.constant 5 (typeNumber sigma))
    (.projection 0) argument (numeral (typeNumber sigma)) parameter xs
    (projectionValue 3 xs) (constantValue 5 (typeNumber sigma) xs)
    (projectionValue 0 xs) (andRight h3)
  exact andIntro (contextRecover context xs (andLeft h0))
    (andIntro (coordinateRecover 5 1 (typeNumber sigma) xs (andLeft h1))
      (andIntro (coordinateRecover 5 2 (typeNumber tau) xs (andLeft h2)) (andIntro hx ha)))

theorem invariantAccept (context : Nat) (data : Data) (sigma tau : Ty)
    (parameter domain codomain argument value : OTerm α)
    (h : Nonempty (Derivation body Delta
      (invariantFactors context data sigma tau parameter domain codomain argument value))) :
    Nonempty (Derivation body Delta
      (programGraph (invariant context data sigma tau) (suc z)
        (arguments parameter domain codomain argument value))) := by
  let xs := arguments parameter domain codomain argument value
  have hx := typedValue data (.projection 4) (Path.constant 5 (typeNumber (.arrow sigma tau)))
    (.projection 0) value (numeral (typeNumber (.arrow sigma tau))) parameter xs
    (projectionValue 4 xs) (constantValue 5 (typeNumber (.arrow sigma tau)) xs)
    (projectionValue 0 xs) (andLeft (andRight (andRight (andRight h))))
  have ha := typedValue data (.projection 3) (Path.constant 5 (typeNumber sigma))
    (.projection 0) argument (numeral (typeNumber sigma)) parameter xs
    (projectionValue 3 xs) (constantValue 5 (typeNumber sigma) xs)
    (projectionValue 0 xs) (andRight (andRight (andRight (andRight h))))
  exact conjunctionAccept _ _ xs (contextAccept context xs (andLeft h))
    (conjunctionAccept _ _ xs (coordinateAccept 5 1 (typeNumber sigma) xs (andLeft (andRight h)))
      (conjunctionAccept _ _ xs (coordinateAccept 5 2 (typeNumber tau) xs (andLeft (andRight (andRight h))))
        (conjunctionAccept _ _ xs hx ha)))

theorem invariantPreserve (context : Nat) (data : Data) (oldStep : Program 4) (sigma tau : Ty)
    (parameter domain codomain argument x y certificate : OTerm α)
    (hi : Nonempty (Derivation body Delta
      (programGraph (invariant context data sigma tau) (suc z)
        (arguments parameter domain codomain argument x))))
    (he : Nonempty (Derivation body Delta (edgeAccepted data oldStep x y certificate parameter))) :
    Nonempty (Derivation body Delta
      (programGraph (invariant context data sigma tau) (suc z)
        (arguments parameter domain codomain argument y))) := by
  have hf := invariantRecover context data sigma tau parameter domain codomain argument x hi
  have hy := TypingProof.typedPropagation data oldStep x y certificate
    (numeral (typeNumber (.arrow sigma tau))) parameter
    (andLeft (andRight (andRight (andRight hf)))) he
  exact invariantAccept context data sigma tau parameter domain codomain argument y
    (andIntro (andLeft hf) (andIntro (andLeft (andRight hf))
      (andIntro (andLeft (andRight (andRight hf)))
        (andIntro hy (andRight (andRight (andRight (andRight hf))))))))

theorem invariantPreservation (context : Nat) (data : Data) (oldStep : Program 4)
    (sigma tau : Ty) :
    InternalParameterizedApplicationPathLift.InvariantPreservation body (edgeChecker data oldStep)
      (invariant context data sigma tau) := by
  intro α ps x y certificate
  let premise := InternalParameterizedApplicationPathLift.invariantAt (invariant context data sigma tau) ps x ⊓
    InternalParameterizedPathChecker.edgeGraph (edgeChecker data oldStep) x y certificate (ps 0)
  have hp : Nonempty (Derivation body [premise] premise) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := invariantPreserve context data oldStep sigma tau (ps 0) (ps 1) (ps 2) (ps 3)
    x y certificate (andLeft hp) (andRight hp)
  exact ⟨Derivation.implicationIntroduction hr⟩

/-- Only a CLOSED numeral computation of the original calibrated window
test is used. No semantic fact about a symbolic Gamma is reflected. -/
theorem closedWindow (n : Nat) (window : Program 1) (hw : windowCalibrated n window)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) :
    Nonempty (Derivation body Delta
      (graph1 window (suc z) (numeral (OrdinaryArithmeticQuotient.contextCode symbols S table)))) := by
  let k := OrdinaryArithmeticQuotient.contextCode symbols S table
  have hv : evaluate window (List.Vector.ofFn ![k]) = 1 := by
    rw [hw]
    exact (GuardCalibrationProof.actualOriginalWindowCalibration n symbols S table).mpr hS
  exact GuardedSourceCertificateProof.windowNumeral (body := body) (Gamma := Delta) window k hv

theorem invariantActivation (n : Nat) (window : Program 1) (hw : windowCalibrated n window)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (data : Data) (sigma tau : Ty)
    (parameter domain codomain argument value : OTerm α)
    (hi : Nonempty (Derivation body Delta
      (programGraph (invariant (OrdinaryArithmeticQuotient.contextCode symbols S table) data sigma tau)
        (suc z) (arguments parameter domain codomain argument value)))) :
    Nonempty (Derivation body Delta
      (programGraph (activation data window) (suc z)
        (arguments parameter domain codomain argument value))) := by
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let xs := arguments parameter domain codomain argument value
  have hf := invariantRecover context data sigma tau parameter domain codomain argument value hi
  have hc := andLeft hf
  have hd := andLeft (andRight hf)
  have he := andLeft (andRight (andRight hf))
  have hx := andLeft (andRight (andRight (andRight hf)))
  have ha := andRight (andRight (andRight (andRight hf)))
  have hwindow := unaryValue window (leftOf (.projection (0 : Fin 5))) (suc z) (numeral context) xs
    (closedWindow n window hw symbols S table hS)
    (unaryValue InternalUnpair.left (.projection (0 : Fin 5)) (numeral context) parameter xs
      hc (projectionValue 0 xs))
  have har := InternalTypedEdgePresentationSupportProof.arrowNumeral (body := body) (Gamma := Delta) (α := α)
    sigma tau
  have har' : Nonempty (Derivation body Delta
      (graph2 InternalListCodec.consCode (numeral (typeNumber (.arrow sigma tau))) domain codomain)) := by
    apply graphInputTransport body α 2 Delta (OrdinaryArithmetic.graphFormula InternalListCodec.consCode)
      (numeral (typeNumber (.arrow sigma tau)))
      (Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau)) Fin.elim0))
      (Fin.cons domain (Fin.cons codomain Fin.elim0)) _ har
    intro i
    exact Fin.cases (equalReverse domain (numeral (typeNumber sigma)) hd)
      (Fin.cases (equalReverse codomain (numeral (typeNumber tau)) he) (fun j => Fin.elim0 j)) i
  have harp := binaryValue InternalListCodec.consCode (.projection 1) (.projection 2)
    (numeral (typeNumber (.arrow sigma tau))) domain codomain xs har'
    (projectionValue 1 xs) (projectionValue 2 xs)
  have hfun := typedValue data (.projection 4) (consOf (.projection 1) (.projection 2)) (.projection 0)
    value (numeral (typeNumber (.arrow sigma tau))) parameter xs
    (projectionValue 4 xs) harp (projectionValue 0 xs) hx
  have ha' : Nonempty (Derivation body Delta (typedAccepted data argument domain parameter)) := by
    apply graphInputTransport body α 3 Delta
      (OrdinaryArithmetic.graphFormula (InternalOriginalUniformDescentSelection.selectedTyped data)) (suc z)
      (Fin.cons argument (Fin.cons (numeral (typeNumber sigma)) (Fin.cons parameter Fin.elim0)))
      (Fin.cons argument (Fin.cons domain (Fin.cons parameter Fin.elim0))) _ ha
    intro i
    exact Fin.cases (equalReflexive argument)
      (Fin.cases (equalReverse domain (numeral (typeNumber sigma)) hd)
        (Fin.cases (equalReflexive parameter) (fun j => Fin.elim0 j))) i
  have harg := typedValue data (.projection 3) (.projection 1) (.projection 0)
    argument domain parameter xs (projectionValue 3 xs) (projectionValue 1 xs) (projectionValue 0 xs) ha'
  exact conjunctionAccept _ _ xs hwindow (conjunctionAccept _ _ xs hfun harg)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathInvariantProof
