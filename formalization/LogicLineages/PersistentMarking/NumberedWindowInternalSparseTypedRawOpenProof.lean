module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawProjectionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseTypedRaw
open NumberedWindowInternalSparseTypedRawTargets
open NumberedWindowInternalSparseTypedRawProjectionProof (projectOne projectThree)

theorem graph : ExactOpenTypedRaw5 := by
  intro body root other wp syn α Γ ctx ty q w r
  let xs : Fin 5 → OTerm α := ![ctx,ty,q,w,r]
  let sq := sourceSyntax syn
  let sr := destinationSyntax syn
  let own := ownCheck root other
  let wq := sourceWindow wp
  let wr := destinationWindow wp
  let syntaxBoth := conjunction sq sr
  let rawPart := conjunction syntaxBoth own
  let windowBoth := conjunction wq wr
  let rawGraph := programGraph (typedRaw5 root other wp syn) (suc z) xs
  let five :=
    ((programGraph syn (suc z) ![q] ⊓ programGraph syn (suc z) ![r]) ⊓
      programGraph (ownRun root other) (suc z) ![q,w,r]) ⊓
    (programGraph wp (suc z) ![ctx,ty,q] ⊓ programGraph wp (suc z) ![ctx,ty,r])
  have toFive : Nonempty (Derivation body (rawGraph :: Γ) five) := by
    let Δ := rawGraph :: Γ
    have accepted : Nonempty (Derivation body Δ rawGraph) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨bits⟩ := conjunctionRecover rawPart windowBoth xs accepted
    obtain ⟨rawBits⟩ := conjunctionRecover syntaxBoth own xs
      ⟨Derivation.conjunctionLeft bits⟩
    obtain ⟨synBits⟩ := conjunctionRecover sq sr xs
      ⟨Derivation.conjunctionLeft rawBits⟩
    obtain ⟨windowBits⟩ := conjunctionRecover wq wr xs
      ⟨Derivation.conjunctionRight bits⟩
    obtain ⟨a⟩ := (projectOne (body := body) (Γ := Δ) syn 2 xs).mp
      ⟨Derivation.conjunctionLeft synBits⟩
    obtain ⟨b⟩ := (projectOne (body := body) (Γ := Δ) syn 4 xs).mp
      ⟨Derivation.conjunctionRight synBits⟩
    obtain ⟨c⟩ := (projectThree (body := body) (Γ := Δ) (ownRun root other) 2 3 4 xs).mp
      ⟨Derivation.conjunctionRight rawBits⟩
    obtain ⟨d⟩ := (projectThree (body := body) (Γ := Δ) wp 0 1 2 xs).mp
      ⟨Derivation.conjunctionLeft windowBits⟩
    obtain ⟨e⟩ := (projectThree (body := body) (Γ := Δ) wp 0 1 4 xs).mp
      ⟨Derivation.conjunctionRight windowBits⟩
    exact ⟨Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction a b) c)
      (Derivation.conjunctionIntroduction d e)⟩
  have toGraph : Nonempty (Derivation body (five :: Γ) rawGraph) := by
    let Δ := five :: Γ
    have given : Derivation body Δ five := Derivation.hypothesis List.mem_cons_self
    have rawBits := Derivation.conjunctionLeft given
    have winBits := Derivation.conjunctionRight given
    have synBits := Derivation.conjunctionLeft rawBits
    have a := (projectOne (body := body) (Γ := Δ) syn 2 xs).mpr
      ⟨Derivation.conjunctionLeft synBits⟩
    have b := (projectOne (body := body) (Γ := Δ) syn 4 xs).mpr
      ⟨Derivation.conjunctionRight synBits⟩
    have c := (projectThree (body := body) (Γ := Δ) (ownRun root other) 2 3 4 xs).mpr
      ⟨Derivation.conjunctionRight rawBits⟩
    have d := (projectThree (body := body) (Γ := Δ) wp 0 1 2 xs).mpr
      ⟨Derivation.conjunctionLeft winBits⟩
    have e := (projectThree (body := body) (Γ := Δ) wp 0 1 4 xs).mpr
      ⟨Derivation.conjunctionRight winBits⟩
    have hRaw := conjunctionAccept syntaxBoth own xs (conjunctionAccept sq sr xs a b) c
    exact conjunctionAccept rawPart windowBoth xs hRaw (conjunctionAccept wq wr xs d e)
  obtain ⟨forward⟩ := toFive
  obtain ⟨backward⟩ := toGraph
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawOpenProof
