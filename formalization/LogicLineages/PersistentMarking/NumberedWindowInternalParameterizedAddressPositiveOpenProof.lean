module

public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositiveOpenCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenSelectorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenSideProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenMatchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositiveOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Rename)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenTapeProof (args slotIntro)
open NumberedWindowInternalSparseAddressPositiveOpenSelectorProof (choose)
open NumberedWindowInternalSparseAddressPositiveOpenSideProof (sideRead sideIntro align)
open NumberedWindowInternalSparseAddressPositiveOpenMatchProof (readSame introSame)
open NumberedWindowInternalParameterizedAddressPositive (addressAt)
open NumberedWindowInternalParameterizedAddressPositiveOpenCoreProof (foldRead foldIntro gateRead gateIntro)

/-- Actual tag-three shells, actual shared readouts, typed scope bits,
and the exact original physical P tape. None is inferred from raw
numeric equality or assumed for invalid/unaccepted addresses. -/
@[expose] def AddressAtReport {α : Type} (cv tv : Program 1) (P : Program 5)
    (left cert right ctx ty src dst : OTerm α) : Formula α :=
  addressReport left ctx ty src ⊓
    (addressReport right ctx ty dst ⊓
      (unary cv (suc z) ctx ⊓
        (unary tv (suc z) ty ⊓ programGraph P (suc z) ![ctx,ty,src,cert,dst])))

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Open both original physical address shells and the actual fold.
Only the physical address checking AST is used; P is arbitrary. -/
theorem exact_OpenAddressAtCases (cv tv : Program 1) (P : Program 5)
    (left cert right : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation B Γ (programGraph (addressAt cv tv P) (suc z) ![left,cert,right])))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (c t src dst : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ
        (AddressAtReport cv tv P (left.relabel j) (cert.relabel j) (right.relabel j) c t src dst)) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply choose left cert right goal
  intro β j Δ ys keep observed
  let xs := args (left.relabel j) (cert.relabel j) (right.relabel j)
  have aligned := renameInto held j Δ keep
  rw [graph3Rename,sucRelabel,zRelabel] at aligned
  obtain ⟨l,r,c,t,f⟩ := gateRead cv tv P xs aligned
  obtain ⟨lRep,cValid,tValid⟩ := sideRead cv tv 0 xs (ys 0) (ys 1) (ys 2) l
    (observed 0) (observed 1) (observed 2)
  obtain ⟨rRep,_,_⟩ := sideRead cv tv 2 xs (ys 3) (ys 4) (ys 5) r
    (observed 3) (observed 4) (observed 5)
  obtain ⟨ce⟩ := readSame rawContext xs (ys 0) (ys 3) (observed 0) (observed 3) c
  obtain ⟨te⟩ := readSame rawResult xs (ys 1) (ys 4) (observed 1) (observed 4) t
  have rightSame := align (right.relabel j) (ys 3) (ys 4) (ys 0) (ys 1) (ys 5)
    ⟨symm ce⟩ ⟨symm te⟩ rRep
  have path := foldRead P xs (ys 0) (ys 1) (ys 2) (ys 5)
    (observed 0) (observed 1) (observed 2) (observed 5) f
  obtain ⟨lrep⟩ := lRep
  obtain ⟨rrep⟩ := rightSame
  obtain ⟨pc⟩ := cValid
  obtain ⟨pt⟩ := tValid
  obtain ⟨pf⟩ := path
  exact next β j Δ (ys 0) (ys 1) (ys 2) (ys 5) keep
    ⟨Derivation.conjunctionIntroduction lrep (Derivation.conjunctionIntroduction rrep
      (Derivation.conjunctionIntroduction pc (Derivation.conjunctionIntroduction pt pf)))⟩

/-- Introduce genuine wrapped address acceptance from the actual held
paired physical fields, scope and P acceptance on that same tape. -/
theorem exact_OpenAddressAtIntro (cv tv : Program 1) (P : Program 5)
    (left cert right c t src dst : OTerm α)
    (read : Nonempty (Derivation B Γ (AddressAtReport cv tv P left cert right c t src dst))) :
    Nonempty (Derivation B Γ (programGraph (addressAt cv tv P) (suc z) ![left,cert,right])) := by
  obtain ⟨u⟩ := read
  let xs := args left cert right
  let l : Derivation B Γ (addressReport left c t src) := Derivation.conjunctionLeft u
  let r : Derivation B Γ (addressReport right c t dst) :=
    Derivation.conjunctionLeft (Derivation.conjunctionRight u)
  let valid := Derivation.conjunctionRight (Derivation.conjunctionRight u)
  let cv' : Nonempty (Derivation B Γ (unary cv (suc z) c)) := ⟨Derivation.conjunctionLeft valid⟩
  let tv' : Nonempty (Derivation B Γ (unary tv (suc z) t)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight valid)⟩
  have leftCtx := slotIntro rawContext 0 c xs ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight l)⟩
  have rightCtx := slotIntro rawContext 2 c xs ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight r)⟩
  have leftTy := slotIntro rawResult 0 t xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight l))⟩
  have rightTy := slotIntro rawResult 2 t xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight r))⟩
  have leftClass := slotIntro rawLeast 0 src xs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight l))⟩
  have rightClass := slotIntro rawLeast 2 dst xs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight r))⟩
  have fold := foldIntro P xs c t src dst leftCtx leftTy leftClass rightClass
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight valid)⟩
  exact gateIntro cv tv P xs ⟨sideIntro cv tv 0 xs c t src ⟨l⟩ cv' tv',
    sideIntro cv tv 2 xs c t dst ⟨r⟩ cv' tv',
    introSame rawContext xs c leftCtx rightCtx,introSame rawResult xs t leftTy rightTy,fold⟩

#print axioms exact_OpenAddressAtCases
#print axioms exact_OpenAddressAtIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositiveOpenProof
