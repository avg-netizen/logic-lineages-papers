module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositiveOpenCoreProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonNilProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenSideProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenMatchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopCoreProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue equalEqn)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons unary)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalParameterizedAddressPositive (addressAt)
open NumberedWindowInternalParameterizedAddressPositiveOpenCoreProof (foldIntro gateIntro)
open NumberedWindowInternalSparseAddressPositiveOpenTapeProof (slotIntro)
open NumberedWindowInternalSparseAddressPositiveOpenSideProof (sideIntro)
open NumberedWindowInternalSparseAddressPositiveOpenMatchProof (introSame)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (tripleTerm reports)
open NumberedWindowInternalDirectWitnessEnvelope (exactOpenTriple)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph)
open NumberedWindowInternalSparseAddressSingletonNilProof (finishNil)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (headData positiveAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionWitnessProof (provideHead)
open NumberedWindowInternalSparsePositiveHeadDecompositionChecks (exact_OpenPositiveHeadDecomposition)

attribute [local irreducible] programGraph

/-- The original middle field is a single raw hop. Feed its exact
one-cell spelling to the unchanged physical address program. -/
def oneHopProgram (R : Program 3) : Program 3 :=
  .composition R ![.projection 0,.composition fieldCons ![.projection 1,constantZero 3],.projection 2]

def literalAddress {α : Type} (c t k : OTerm α) : OTerm α := tripleTerm 3 c t k

abbrev D {α : Type} (B : Positive (Fin 1)) (Γ : List (Formula α)) (p : Formula α) :=
  Nonempty (Derivation B Γ p)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OriginalLiteralAddressReport (c t k : OTerm α) :
    D B Γ (addressReport (literalAddress c t k) c t k) := by
  let term := literalAddress c t k
  obtain ⟨law⟩ := exactOpenTriple B α Γ 3 term c t k
  have self : Derivation B Γ (equal term (tripleTerm 3 c t k)) := by
    rw [equalEqn]
    change Derivation B Γ (ID1Completion.InternalTagArithmeticSyntaxProof.eqn (tripleTerm 3 c t k) (tripleTerm 3 c t k))
    exact ID1Completion.InternalTagArithmeticSupportProof.refl (tripleTerm 3 c t k)
  have facts : Derivation B Γ (reports 3 term c t k) :=
    Derivation.implicationElimination (Derivation.conjunctionLeft law) self
  exact ⟨facts⟩

/-- Introduce the parameterized original address checker at the
literal reported endpoints with the very same context/type guards. -/
theorem exact_OriginalAddressAtIntro (cv tv : Program 1) (P : Program 5)
    (x cert y c ty src dst : OTerm α)
    (left : D B Γ (addressReport x c ty src)) (right : D B Γ (addressReport y c ty dst))
    (g₀ : D B Γ (unary cv (suc z) c)) (g₁ : D B Γ (unary tv (suc z) ty))
    (called : D B Γ (programGraph P (suc z) ![c,ty,src,cert,dst])) :
    D B Γ (programGraph (addressAt cv tv P) (suc z) ![x,cert,y]) := by
  let xs : Fin 3 → OTerm α := ![x,cert,y]
  obtain ⟨l⟩ := left
  obtain ⟨r⟩ := right
  have lc := slotIntro rawContext 0 c xs ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight l)⟩
  have rc := slotIntro rawContext 2 c xs ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight r)⟩
  have lt := slotIntro rawResult 0 ty xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight l))⟩
  have rt := slotIntro rawResult 2 ty xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight r))⟩
  have ls := slotIntro rawLeast 0 src xs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight l))⟩
  have rs := slotIntro rawLeast 2 dst xs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight r))⟩
  exact gateIntro cv tv P xs ⟨sideIntro cv tv 0 xs c ty src ⟨l⟩ g₀ g₁,
    sideIntro cv tv 2 xs c ty dst ⟨r⟩ g₀ g₁,introSame rawContext xs c lc rc,
    introSame rawResult xs ty lt rt,foldIntro P xs c ty src dst lc lt ls rs called⟩

/-- Reuse an accepted physical raw advance as a one-cell positive
certificate, using the actual finite chosen-fuel finish at nil. -/
theorem exact_OriginalPositiveOneCell (raw : Program 5) (least : Program 3)
    (c ty src hd dst : OTerm α)
    (advanced : D B Γ (selectedGraph raw least (suc dst) c ty (suc src) hd)) :
    D B Γ (positiveAt raw least c ty src (rawCons hd z) dst) := by
  let cert := rawCons hd z
  obtain ⟨cell⟩ := NumberedWindowInternalSparsePairGraphProof.consGraph (body := B) (Γ := Γ) hd z
  obtain ⟨accepted⟩ := advanced
  obtain ⟨nil⟩ := finishNil (body := B) (Γ := Γ) raw least c ty dst
  have row : D B Γ (headData raw least c ty src cert dst hd z dst) :=
    ⟨Derivation.conjunctionIntroduction cell (Derivation.conjunctionIntroduction accepted nil)⟩
  have ex := provideHead raw least c ty src cert dst hd z dst row
  obtain ⟨eq⟩ := exact_OpenPositiveHeadDecomposition B raw least α c ty src cert dst
  exact closedApply ⟨Derivation.conjunctionRight eq⟩ ex

theorem exact_OneHopProgramIntro (R : Program 3) (x hd y : OTerm α)
    (held : D B Γ (programGraph R (suc z) ![x,rawCons hd z,y])) :
    D B Γ (programGraph (oneHopProgram R) (suc z) ![x,hd,y]) := by
  let xs : Fin 3 → OTerm α := ![x,hd,y]
  have oneCell : D B Γ (programGraph (.composition fieldCons ![.projection 1,constantZero 3])
      (rawCons hd z) xs) := by
    apply compositionValue fieldCons ![.projection 1,constantZero 3] (rawCons hd z) xs ![hd,z]
      (NumberedWindowInternalSparsePairGraphProof.consGraph hd z)
    intro k
    exact Fin.cases (projectionValue 1 xs)
      (Fin.cases (constantZeroValue xs) (fun q => Fin.elim0 q)) k
  apply compositionValue R ![.projection 0,.composition fieldCons ![.projection 1,constantZero 3],
    .projection 2] (suc z) xs ![x,rawCons hd z,y] held
  intro k
  exact Fin.cases (projectionValue 0 xs)
    (Fin.cases oneCell (Fin.cases (projectionValue 2 xs) (fun q => Fin.elim0 q))) k

#print axioms exact_OriginalLiteralAddressReport
#print axioms exact_OriginalAddressAtIntro
#print axioms exact_OriginalPositiveOneCell
#print axioms exact_OneHopProgramIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopCoreProof
