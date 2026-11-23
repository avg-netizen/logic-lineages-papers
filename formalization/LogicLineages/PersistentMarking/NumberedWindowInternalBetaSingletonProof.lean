module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatchOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerOpenIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunRootProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaSingletonProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalSparseRawRunRootProof (rootRunAccept)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalSparsePathAdvanceTargets (actualCalls)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalSparseAddressSingletonCoreProof (fromCalls)
open NumberedWindowInternalBetaSub (betaChecker)
open NumberedWindowInternalBetaRootDispatch (root')

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Carry the actual β root step into the genuine raw validator at the
original doubly tagged witness, without a numerical reflection rule. -/
theorem typedBeta (original other windowProg : Program 3) (syn : Program 1)
    (guard arg body sub : Program 2) (ctx ty q r a v : OTerm α)
    (guardYes : Nonempty (Derivation B Γ (programGraph guard (suc z) ![q,r])))
    (argRead : Nonempty (Derivation B Γ (programGraph arg a ![q,r])))
    (bodyRead : Nonempty (Derivation B Γ (programGraph body v ![q,r])))
    (result : Nonempty (Derivation B Γ (programGraph sub (suc r) ![a,v])))
    (qSyntax : Nonempty (Derivation B Γ (programGraph syn (suc z) ![q])))
    (rSyntax : Nonempty (Derivation B Γ (programGraph syn (suc z) ![r])))
    (qWindow : Nonempty (Derivation B Γ (programGraph windowProg (suc z) ![ctx,ty,q])))
    (rWindow : Nonempty (Derivation B Γ (programGraph windowProg (suc z) ![ctx,ty,r]))) :
    let root := root' original (betaChecker guard arg body sub)
    let w := rootWitnessTerm (rawCons (numeral 6) z)
    Nonempty (Derivation B Γ (programGraph (typedRaw5 root other windowProg syn)
      (suc z) ![ctx,ty,q,w,r])) := by
  let root := root' original (betaChecker guard arg body sub)
  let payload : OTerm α := rawCons (numeral 6) z
  let w := rootWitnessTerm payload
  have checked := NumberedWindowInternalBetaCheckerOpenIntroProof.accept guard arg body sub
    q r a v guardYes argRead bodyRead result
  have rootChecked := NumberedWindowInternalBetaRootDispatchOpenProof.accept original
    (betaChecker guard arg body sub) q r checked
  obtain ⟨own⟩ := rootRunAccept root other q payload r rootChecked
  obtain ⟨shape⟩ := exact_OpenTypedRaw5 B root other windowProg syn α Γ ctx ty q w r
  obtain ⟨qs⟩ := qSyntax
  obtain ⟨rs⟩ := rSyntax
  obtain ⟨qw⟩ := qWindow
  obtain ⟨rw⟩ := rWindow
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight shape)
    (Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction qs rs) own)
      (Derivation.conjunctionIntroduction qw rw))⟩

/-- Actual positive tape with exactly one β hop. Held successful least
reports identify both endpoint classes at the same context and type. -/
theorem singleton (original other windowProg least : Program 3) (syn : Program 1)
    (guard arg body sub : Program 2) (ctx ty src dst q r : OTerm α) :
    let root := root' original (betaChecker guard arg body sub)
    let raw := typedRaw5 root other windowProg syn
    let w := rootWitnessTerm (rawCons (numeral 6) z)
    Nonempty (Derivation B Γ (programGraph raw (suc z) ![ctx,ty,q,w,r])) →
    Nonempty (Derivation B Γ (programGraph least (suc src) ![ctx,ty,q])) →
    Nonempty (Derivation B Γ (programGraph least (suc dst) ![ctx,ty,r])) →
    Nonempty (Derivation B Γ (positiveAt raw least ctx ty src (singletonCertificate dst q w r) dst)) := by
  intro root raw w h qLeast rLeast
  obtain ⟨h⟩ := h
  obtain ⟨ql⟩ := qLeast
  obtain ⟨rl⟩ := rLeast
  have reports : Nonempty (Derivation B Γ (actualCalls raw least ctx ty src dst q w r)) :=
    ⟨Derivation.conjunctionIntroduction h (Derivation.conjunctionIntroduction ql rl)⟩
  exact fromCalls raw least ctx ty src dst q w r reports

#print axioms typedBeta
#print axioms singleton
end LogicLineages.PersistentMarking.NumberedWindowInternalBetaSingletonProof
