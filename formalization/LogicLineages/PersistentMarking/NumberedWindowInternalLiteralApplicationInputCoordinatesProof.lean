module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationFormationSeamProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressFieldsThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationInputCoordinatesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseCanonicalAddressFieldsThinProof (reported)
open NumberedWindowInternalSparseCanonicalCoordinatesLiteralThinProof (openTest)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalLiteralApplicationFormationSeamProof (SelectedSeedFormation)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fieldsValid (cv tv : Program 1) (W L : Program 3) (q ctx ty k : OTerm α)
    (shell : D B Γ (addressReport q ctx ty k))
    (scalar : D B Γ (unary (addressScalar cv tv W L) (suc z) q)) :
    D B Γ (unary cv (suc z) ctx) ∧ D B Γ (unary tv (suc z) ty) ∧ D B Γ (windowAt W ctx ty k) := by
  obtain ⟨f⟩ := reported cv tv W L B α Γ q ctx ty k
  obtain ⟨atQ⟩ := shell
  obtain ⟨ok⟩ := scalar
  let got := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination f atQ)) ok
  obtain ⟨g⟩ := openTest W L B α Γ ctx ty k
  let valid := Derivation.implicationElimination (Derivation.conjunctionLeft g)
    (Derivation.conjunctionRight (Derivation.conjunctionRight got))
  exact ⟨⟨Derivation.conjunctionLeft got⟩,
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight got)⟩,⟨Derivation.conjunctionLeft valid⟩⟩

private theorem windowReplaceType (W : Program 3) (ctx ty other raw : OTerm α)
    (eq : D B Γ (eqn ty other)) (held : D B Γ (windowAt W ctx ty raw)) :
    D B Γ (windowAt W ctx other raw) := by
  unfold windowAt at held ⊢
  unfold programGraph at held ⊢
  apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula W) (suc z)
    ![ctx,ty,raw] ![ctx,other,raw] _ held
  intro j
  rw [onEquality]
  change D B Γ (eqn ((![ctx,ty,raw] : Fin 3 → OTerm α) j) ((![ctx,other,raw] : Fin 3 → OTerm α) j))
  have same (t : OTerm α) : D B Γ (eqn t t) := ⟨ID1Completion.InternalTagArithmeticSupportProof.refl t⟩
  exact Fin.cases (same ctx) (Fin.cases eq (Fin.cases (same raw) (fun i => Fin.elim0 i))) j

/-- Decompose the successful scalar checks at the two real application
inputs. In the very same selected window, the actual child coordinates
satisfy both windows and both requested type checks, and the shared
packed context is accepted by the installed context validator. -/
theorem exact_OpenLiteralApplicationInputCoordinates (cv tv : Program 1) (W L : Program 3)
    (f u ctx r dom cod fn arg : OTerm α)
    (left : D B Γ (unary (addressScalar cv tv W L) (suc z) f))
    (right : D B Γ (unary (addressScalar cv tv W L) (suc z) u))
    (parsed : D B Γ (parsedApplicationInputs f u ctx r dom cod fn arg)) :
    D B Γ (unary cv (suc z) ctx) ∧
      D B Γ (unary tv (suc z) (rawCons dom cod)) ∧ D B Γ (unary tv (suc z) dom) ∧
      D B Γ (windowAt W ctx (rawCons dom cod) fn) ∧ D B Γ (windowAt W ctx dom arg) := by
  obtain ⟨all⟩ := parsed
  let urs := Derivation.conjunctionRight all
  let arrow := Derivation.conjunctionRight urs
  let fs := Derivation.conjunctionRight arrow
  let us := Derivation.conjunctionRight fs
  let ars := Derivation.conjunctionRight us
  let lit := Derivation.conjunctionRight ars
  let coord := Derivation.conjunctionRight lit
  let req := Derivation.conjunctionLeft coord
  have lf : D B Γ (addressReport f ctx r fn) := ⟨Derivation.conjunctionIntroduction
    (Derivation.conjunctionLeft all) (Derivation.conjunctionLeft fs)⟩
  have ru : D B Γ (addressReport u ctx dom arg) := ⟨Derivation.conjunctionIntroduction
    (Derivation.conjunctionLeft urs) (Derivation.conjunctionLeft us)⟩
  obtain ⟨gc,ty,winf⟩ := fieldsValid cv tv W L f ctx r fn lf left
  obtain ⟨_,domOk,winu⟩ := fieldsValid cv tv W L u ctx dom arg ru right
  have arrowOk := headTransport tv (suc z) r (rawCons dom cod) ![] ⟨req⟩ ty
  exact ⟨gc,arrowOk,domOk,windowReplaceType W ctx r (rawCons dom cod) fn ⟨req⟩ winf,winu⟩

/-- Separate the two remaining exact choices: codomain validation in
the installed tv and formation of the auxiliary in the installed W.
Every input to these choices comes from the actual application report. -/
theorem exact_LiteralApplicationSeedFormationFromChildren (cv tv : Program 1) (W L : Program 3)
    (typeCodomain : ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (dom cod : OTerm α),
      D B Γ (unary tv (suc z) (rawCons dom cod)) → D B Γ (unary tv (suc z) cod))
    (auxWindow : ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
      (ctx dom cod fn arg k : OTerm α),
      D B Γ (unary cv (suc z) ctx) →
      D B Γ (unary tv (suc z) (rawCons dom cod)) → D B Γ (unary tv (suc z) dom) →
      D B Γ (unary tv (suc z) cod) →
      D B Γ (windowAt W ctx (rawCons dom cod) fn) → D B Γ (windowAt W ctx dom arg) →
      D B Γ (programGraph L (suc k) ![ctx,cod,auxiliaryTerm dom cod fn arg]) →
      D B Γ (windowAt W ctx cod (auxiliaryTerm dom cod fn arg))) :
    SelectedSeedFormation (addressScalar cv tv W L) cv tv W L := by
  intro body a gamma f u ctx r dom cod fn arg k fnOK argOK parsed least
  obtain ⟨gc,arr,d,wf,wa⟩ := exact_OpenLiteralApplicationInputCoordinates cv tv W L
    f u ctx r dom cod fn arg fnOK argOK parsed
  have t := typeCodomain body a gamma dom cod arr
  exact ⟨gc,t,auxWindow body a gamma ctx dom cod fn arg k gc arr d t wf wa least⟩

#print axioms exact_OpenLiteralApplicationInputCoordinates
#print axioms exact_LiteralApplicationSeedFormationFromChildren
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationInputCoordinatesProof
