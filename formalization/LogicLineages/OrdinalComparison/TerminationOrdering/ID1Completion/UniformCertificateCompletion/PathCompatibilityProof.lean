module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathInvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathCompatibilityProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open UniformCertificateCompletion.Path UniformCertificateCompletion.PathSupportProof
open UniformCertificateCompletion.PathInvariantProof
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformContextMembership (normalizeData)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionEqualityProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem fiveInputsTransport (p : Program 5) (out : OTerm α) (xs ys : Fin 5 → OTerm α)
    (he : ∀ i, Nonempty (Derivation body Delta (equal (xs i) (ys i))))
    (h : Nonempty (Derivation body Delta (programGraph p out xs))) :
    Nonempty (Derivation body Delta (programGraph p out ys)) :=
  graphInputTransport body α 5 Delta (OrdinaryArithmetic.graphFormula p) out xs ys he h

/-- Recover the original context/Gamma pair from both ORIGINAL projections.
Only its right projection is queried; its Gamma remains symbolic. -/
theorem compatibleWithRight (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hw : windowCalibrated n window)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (oldStep : Program 4) (oldVertex : Program 5)
    (sigma tau : Ty) (ps : InternalParameterizedApplicationPathLift.Parameters α)
    (x y certificate out other lifted gammaCode : OTerm α)
    (hi : Nonempty (Derivation body Delta
      (InternalParameterizedApplicationPathLift.invariantAt
        (invariant (OrdinaryArithmeticQuotient.contextCode symbols S table) (normalizeData base) sigma tau) ps x)))
    (he : Nonempty (Derivation body Delta (edgeAccepted (normalizeData base) oldStep x y certificate (ps 0))))
    (hout : Nonempty (Derivation body Delta
      (InternalParameterizedApplicationPathLift.vertexAt (vertex (normalizeData base) window oldVertex) ps out x)))
    (hother : Nonempty (Derivation body Delta
      (InternalParameterizedApplicationPathLift.vertexAt (vertex (normalizeData base) window oldVertex) ps other y)))
    (hlift : Nonempty (Derivation body Delta
      (InternalParameterizedApplicationPathLift.liftedEdgeAt ps lifted certificate)))
    (hright : Nonempty (Derivation body Delta (graph1 InternalUnpair.right gammaCode (ps 0)))) :
    Nonempty (Derivation body Delta (edgeAccepted (normalizeData base) oldStep out other lifted (ps 0))) := by
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let data := normalizeData base
  have hiy := invariantPreserve context data oldStep sigma tau (ps 0) (ps 1) (ps 2) (ps 3)
    x y certificate hi he
  have hax := invariantActivation n window hw symbols S table hS data sigma tau
    (ps 0) (ps 1) (ps 2) (ps 3) x hi
  have hay := invariantActivation n window hw symbols S table hS data sigma tau
    (ps 0) (ps 1) (ps 2) (ps 3) y hiy
  have hxo := vertexRecover data window oldVertex (arguments (ps 0) (ps 1) (ps 2) (ps 3) x) out hax hout
  have hyo := vertexRecover data window oldVertex (arguments (ps 0) (ps 1) (ps 2) (ps 3) y) other hay hother
  have hf := invariantRecover context data sigma tau (ps 0) (ps 1) (ps 2) (ps 3) x hi
  have hd := andLeft (andRight hf)
  have ht := andLeft (andRight (andRight hf))
  have hpair := reconstructPair (ps 0) (numeral context) gammaCode (andLeft hf) hright
  have hxo' : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.applicationGraph data out
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) x (ps 3) (ps 0))) := by
    apply fiveInputsTransport (InternalParameterizedCanonicalResultFold.actualJ data) out
      (Fin.cons (ps 1) (Fin.cons (ps 2) (Fin.cons x (Fin.cons (ps 3) (Fin.cons (ps 0) Fin.elim0)))))
      (Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau))
        (Fin.cons x (Fin.cons (ps 3) (Fin.cons (ps 0) Fin.elim0))))) _ hxo
    intro i
    exact Fin.cases hd (Fin.cases ht (Fin.cases (equalReflexive x)
      (Fin.cases (equalReflexive (ps 3)) (Fin.cases (equalReflexive (ps 0)) (fun j => Fin.elim0 j))))) i
  have hyo' : Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.applicationGraph data other
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) y (ps 3) (ps 0))) := by
    apply fiveInputsTransport (InternalParameterizedCanonicalResultFold.actualJ data) other
      (Fin.cons (ps 1) (Fin.cons (ps 2) (Fin.cons y (Fin.cons (ps 3) (Fin.cons (ps 0) Fin.elim0)))))
      (Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau))
        (Fin.cons y (Fin.cons (ps 3) (Fin.cons (ps 0) Fin.elim0))))) _ hyo
    intro i
    exact Fin.cases hd (Fin.cases ht (Fin.cases (equalReflexive y)
      (Fin.cases (equalReflexive (ps 3)) (Fin.cases (equalReflexive (ps 0)) (fun j => Fin.elim0 j))))) i
  have hlift' : Nonempty (Derivation body Delta
      (graph4 edgeLift lifted (numeral (typeNumber sigma)) (numeral (typeNumber tau)) (ps 3) certificate)) := by
    apply graphInputTransport body α 4 Delta (OrdinaryArithmetic.graphFormula edgeLift) lifted
      (Fin.cons (ps 1) (Fin.cons (ps 2) (Fin.cons (ps 3) (Fin.cons certificate Fin.elim0))))
      (Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau))
        (Fin.cons (ps 3) (Fin.cons certificate Fin.elim0)))) _ hlift
    intro i
    exact Fin.cases hd (Fin.cases ht (Fin.cases (equalReflexive (ps 3))
      (Fin.cases (equalReflexive certificate) (fun j => Fin.elim0 j)))) i
  have hp : Nonempty (Derivation body Delta
      (Application.liftPremises context data oldStep sigma tau x y (ps 3) certificate
        out other lifted (ps 0) gammaCode)) :=
    andIntro (andIntro hpair
      (andIntro (andLeft (andRight (andRight (andRight hf))))
        (andIntro (andRight (andRight (andRight (andRight hf))))
          (andIntro he (andIntro hxo' hyo'))))) hlift'
  obtain ⟨hrule⟩ := ApplicationProof.actualOriginalUniformApplicationEdgeLift n arity base hc
    symbols S table hS oldStep body α Delta sigma tau x y (ps 3) certificate
    out other lifted (ps 0) gammaCode
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination hrule hp⟩

theorem edgeCompatibility (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (window : Program 1) (hw : windowCalibrated n window)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (oldStep : Program 4) (oldVertex : Program 5)
    (sigma tau : Ty) :
    InternalParameterizedApplicationPathLift.EdgeCompatibility body
      (edgeChecker (normalizeData base) oldStep) (vertex (normalizeData base) window oldVertex)
      (invariant (OrdinaryArithmeticQuotient.contextCode symbols S table) (normalizeData base) sigma tau) := by
  intro α ps x y certificate out other lifted
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let data := normalizeData base
  let premise := InternalParameterizedApplicationPathLift.invariantAt (invariant context data sigma tau) ps x ⊓
    (InternalParameterizedPathChecker.edgeGraph (edgeChecker data oldStep) x y certificate (ps 0) ⊓
      (InternalParameterizedApplicationPathLift.vertexAt (vertex data window oldVertex) ps out x ⊓
        (InternalParameterizedApplicationPathLift.vertexAt (vertex data window oldVertex) ps other y ⊓
          InternalParameterizedApplicationPathLift.liftedEdgeAt ps lifted certificate)))
  have hp : Nonempty (Derivation body [premise] premise) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have result : Nonempty (Derivation body [premise] (edgeAccepted data oldStep out other lifted (ps 0))) := by
    apply programCases InternalUnpair.right (Fin.cons (ps 0) Fin.elim0)
      (edgeAccepted data oldStep out other lifted (ps 0))
    intro β j Theta gammaCode hj hright
    rw [SupportProof.edgeRename]
    simp only [consTermRename,emptyRename] at hright
    have hix := renameInto (andLeft hp) j Theta hj
    rw [InternalApplicationPathLiftSyntaxProof.invariantAtRename] at hix
    have he := renameInto (andLeft (andRight hp)) j Theta hj
    rw [InternalParameterizedPathCheckerSyntaxProof.edgeRename] at he
    have hxo := renameInto (andLeft (andRight (andRight hp))) j Theta hj
    rw [InternalApplicationPathLiftSyntaxProof.vertexAtRename] at hxo
    have hyo := renameInto (andLeft (andRight (andRight (andRight hp)))) j Theta hj
    rw [InternalApplicationPathLiftSyntaxProof.vertexAtRename] at hyo
    have hlift := renameInto (andRight (andRight (andRight (andRight hp)))) j Theta hj
    rw [InternalApplicationPathLiftSyntaxProof.liftedEdgeAtRename] at hlift
    exact compatibleWithRight n arity base hc window hw symbols S table hS oldStep oldVertex sigma tau
      (fun i => (ps i).relabel j) (x.relabel j) (y.relabel j) (certificate.relabel j)
      (out.relabel j) (other.relabel j) (lifted.relabel j) gammaCode hix he hxo hyo hlift hright
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathCompatibilityProof
