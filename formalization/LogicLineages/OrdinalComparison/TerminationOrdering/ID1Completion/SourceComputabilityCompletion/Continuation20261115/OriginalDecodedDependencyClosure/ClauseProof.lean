module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.ClauseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalContextInsertionSyntaxProof
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open OriginalCodeValidityGuard.FieldProof
open OriginalHeadDecoderValidity.BackwardProof (orCases)
open Continuation20261114
variable {n : Nat} {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {raw : OTerm alpha}
structure Frame (n : Nat) (body : Positive (Fin 1)) (Delta : List (Formula alpha)) (raw : OTerm alpha) where
  tag : OTerm alpha
  payload : OTerm alpha
  first : OTerm alpha
  second : OTerm alpha
  head : OTerm alpha
  deps : OTerm alpha
  child : OTerm alpha
  pair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload))
  firstGraph : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw))
  secondGraph : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw))
  headGraph : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) head raw))
  childrenGraph : Nonempty (Derivation body Delta (graph1 ArgumentEntriesChildren.children deps raw))
  member : Nonempty (Derivation body Delta (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) deps child))
def Frame.withHyp (f : Frame n body Delta raw) (q : Formula alpha) : Frame n body (q :: Delta) raw where
  tag := f.tag
  payload := f.payload
  first := f.first
  second := f.second
  head := f.head
  deps := f.deps
  child := f.child
  pair := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.pair q
  firstGraph := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.firstGraph q
  secondGraph := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.secondGraph q
  headGraph := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.headGraph q
  childrenGraph := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.childrenGraph q
  member := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.member q

def C0 (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 0) ⊔ eqn f.tag (numeral 3)
def C1 (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 1) ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) f.first
def C2 (f : Frame n body Delta raw) : Formula alpha := (eqn f.tag (numeral 2) ⊔ eqn f.tag (numeral 7)) ⊓
  (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) f.first ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) f.second)
def C4 (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 4) ⊓
  (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) f.head ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) f.first)
def C5 (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 5) ⊓
  ((graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) f.head ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) f.first) ⊓
    graph1 (OriginalCodeValidityGuard.check n) (numeral 1) f.second)
def C6 (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 6) ⊓ eqn f.payload z
def goal (f : Frame n body Delta raw) : Formula alpha := graph1 (OriginalCodeValidityGuard.check n) (numeral 1) f.child

theorem at0 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C0 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  have har : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 0) raw)) := by
    apply orCases ha
    · exact arityTag0 (.projection 0) (Fin.cons raw Fin.elim0)
        (OriginalCodeValidityCoherence.DescentProof.tagGraph 0 raw f.tag f.payload (f.withHyp _).pair
          ⟨Derivation.hypothesis List.mem_cons_self⟩)
    · exact arityTag3 (.projection 0) (Fin.cons raw Fin.elim0)
        (OriginalCodeValidityCoherence.DescentProof.tagGraph 3 raw f.tag f.payload (f.withHyp _).pair
          ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact MemberSupportProof.zeroCase raw f.deps f.child har f.childrenGraph f.member

theorem at1 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C1 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  have har : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) raw)) := by
    exact arityTag1 (.projection 0) (Fin.cons raw Fin.elim0)
      (OriginalCodeValidityCoherence.DescentProof.tagGraph 1 raw f.tag f.payload f.pair (andLeft ha))
  exact MemberProof.unary1 raw f.deps f.child f.first har f.childrenGraph f.member f.firstGraph (andRight ha)

theorem at2 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C2 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  have har : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) raw)) := by
    apply orCases (andLeft ha)
    · exact arityTag2 (.projection 0) (Fin.cons raw Fin.elim0)
        (OriginalCodeValidityCoherence.DescentProof.tagGraph 2 raw f.tag f.payload (f.withHyp _).pair
          ⟨Derivation.hypothesis List.mem_cons_self⟩)
    · exact arityTag7 (.projection 0) (Fin.cons raw Fin.elim0)
        (OriginalCodeValidityCoherence.DescentProof.tagGraph 7 raw f.tag f.payload (f.withHyp _).pair
          ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact MemberProof.binary2 raw f.deps f.child f.first f.second har f.childrenGraph f.member f.firstGraph f.secondGraph (andLeft (andRight ha)) (andRight (andRight ha))

theorem at4 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C4 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  have har : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) raw)) := by
    exact arityTag4 (.projection 0) (Fin.cons raw Fin.elim0)
      (OriginalCodeValidityCoherence.DescentProof.tagGraph 4 raw f.tag f.payload f.pair (andLeft ha))
  exact MemberProof.unary1 raw f.deps f.child f.first har f.childrenGraph f.member f.firstGraph (andRight (andRight ha))

theorem at5 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C5 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  have har : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) raw)) := by
    exact arityTag5 (.projection 0) (Fin.cons raw Fin.elim0)
      (OriginalCodeValidityCoherence.DescentProof.tagGraph 5 raw f.tag f.payload f.pair (andLeft ha))
  exact MemberProof.binary2 raw f.deps f.child f.first f.second har f.childrenGraph f.member f.firstGraph f.secondGraph (andRight (andLeft (andRight ha))) (andRight (andRight ha))

theorem at6 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C6 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  have har : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 0) raw)) := by
    exact arityTag6 (.projection 0) (Fin.cons raw Fin.elim0)
      (OriginalCodeValidityCoherence.DescentProof.tagGraph 6 raw f.tag f.payload f.pair (andLeft ha))
  exact MemberSupportProof.zeroCase raw f.deps f.child har f.childrenGraph f.member

def R4 (f : Frame n body Delta raw) : Formula alpha := C5 f ⊔ C6 f
def R3 (f : Frame n body Delta raw) : Formula alpha := C4 f ⊔ R4 f
def R2 (f : Frame n body Delta raw) : Formula alpha := C2 f ⊔ R3 f
def R1 (f : Frame n body Delta raw) : Formula alpha := C1 f ⊔ R2 f

theorem tail4 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (R4 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  apply orCases ha
  · exact at5 (f.withHyp (C5 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact at6 (f.withHyp (C6 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem tail3 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (R3 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  apply orCases ha
  · exact at4 (f.withHyp (C4 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact tail4 (f.withHyp (R4 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem tail2 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (R2 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  apply orCases ha
  · exact at2 (f.withHyp (C2 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact tail3 (f.withHyp (R3 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem tail1 (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (R1 f))) :
    Nonempty (Derivation body Delta (goal f)) := by
  apply orCases ha
  · exact at1 (f.withHyp (C1 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact tail2 (f.withHyp (R2 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem fromAllowed (f : Frame n body Delta raw)
    (ha : Nonempty (Derivation body Delta (OriginalCodeValidityConstructors.Targets.allowed n f.tag f.payload f.first f.second f.head))) :
    Nonempty (Derivation body Delta (goal f)) := by
  change Nonempty (Derivation body Delta (C0 f ⊔ R1 f)) at ha
  apply orCases ha
  · exact at0 (f.withHyp (C0 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact tail1 (f.withHyp (R1 f)) ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.ClauseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.ClauseProof
