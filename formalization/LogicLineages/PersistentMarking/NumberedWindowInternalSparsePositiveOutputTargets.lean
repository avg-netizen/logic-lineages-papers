module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph loopGraph)
open NumberedWindowInternalSparsePositiveFold (chosenState finish chosenWalk positive)

/-- Literal context, type, encoded start, raw certificate order for the
actual chosen-state and finish programs. -/
abbrev args4 {α : Type} (ctx ty current certificate : OTerm α) : Fin 4 → OTerm α :=
  ![ctx,ty,current,certificate]

/-- Literal context, type, original source class, raw certificate and
destination class order for the actual positive checker. -/
abbrev args5 {α : Type} (ctx ty source certificate target : OTerm α) : Fin 5 → OTerm α :=
  ![ctx,ty,source,certificate,target]

def equivalent {α : Type} (p q : Formula α) : Formula α := (p.imp q) ⊓ (q.imp p)

/-- Chosen state uses exactly cert as fuel and retains the same original
raw certificate, not a re-encoded parse or a chosen native bound. -/
def OpenChosenState : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (out ctx ty current certificate : OTerm α),
    Nonempty (Derivation body []
      (equivalent (programGraph (chosenState raw least) out (args4 ctx ty current certificate))
        (loopGraph raw least out certificate ctx ty current certificate)))

/-- Both real finish branches at an actual returned scratch pair. This
contract deliberately takes the genuine pair and loop graph as object
assumptions. It does not prove sufficient-fuel terminality. -/
def OpenFinishAtScratch : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (state ctx ty initial certificate cursor current : OTerm α),
    let haveScratch := loopGraph raw least state certificate ctx ty initial certificate ⊓
      scratchGraph state cursor current
    let done := equal cursor z
    let result := fun value => programGraph (finish raw least) value (args4 ctx ty initial certificate)
    Nonempty (Derivation body [] (haveScratch.imp ((done.imp (result current)) ⊓
      (done.not.imp (result z)))))

/-- The actual walk encodes the original source class by successor and
passes the exact same packed context/type/certificate to original finish. -/
def OpenChosenWalk : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (out ctx ty source certificate unusedTarget : OTerm α),
    Nonempty (Derivation body []
      (equivalent (programGraph (chosenWalk raw least) out (args5 ctx ty source certificate unusedTarget))
        (programGraph (finish raw least) out (args4 ctx ty (suc source) certificate))))

/-- The final actual checker accepts exactly a nonempty raw certificate
whose already terminal result is the genuine successor of the target.
Both implications are object derivations on the same original program. -/
def OpenPositiveAtTerminal : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (state ctx ty source certificate target current : OTerm α),
    let haveTerminal := loopGraph raw least state certificate ctx ty (suc source) certificate ⊓
      scratchGraph state z current
    let accepted := programGraph (positive raw least) (suc z) (args5 ctx ty source certificate target)
    let valid := (equal certificate z).not ⊓ equal current (suc target)
    Nonempty (Derivation body [] (haveTerminal.imp (equivalent accepted valid)))

/-- The genuine positive checker returns zero on literal nil, with no
condition on packed context/type/source/destination or callback values. -/
def OpenPositiveNilReject : Prop :=
  ∀ (body : Positive (Fin 1)) (raw : Program 5) (least : Program 3) (α : Type)
    (ctx ty source target : OTerm α),
    Nonempty (Derivation body [] (programGraph (positive raw least) z (args5 ctx ty source z target)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTargets
