module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.ChildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.ClauseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalContextInsertionSyntaxProof
open OriginalRawSyntaxTransport
open OriginalCodeValidityGuard.FieldProof
open OriginalHeadDecoderValidity.BackwardProof (orCases)
variable {n : Nat} {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)} {raw : OTerm alpha}
structure Frame (n : Nat) (body : Positive (Fin 1)) (Delta : List (Formula alpha)) (raw : OTerm alpha) where
  previous : OTerm alpha
  tag : OTerm alpha
  payload : OTerm alpha
  first : OTerm alpha
  second : OTerm alpha
  head : OTerm alpha
  prior : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderTable.tableProgram n) previous raw raw))
  pair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload))
  firstGraph : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw))
  secondGraph : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw))
  headGraph : Nonempty (Derivation body Delta (graph1 (headOf (.projection 0)) head raw))
def Frame.withHyp (f : Frame n body Delta raw) (q : Formula alpha) : Frame n body (q :: Delta) raw where
  previous := f.previous
  tag := f.tag
  payload := f.payload
  first := f.first
  second := f.second
  head := f.head
  prior := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.prior q
  pair := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.pair q
  firstGraph := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.firstGraph q
  secondGraph := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.secondGraph q
  headGraph := InternalApplicationValidityStackAppendInductionCoreProof.withHyp f.headGraph q

def accepted (own : Bool) (f : Frame n body Delta raw) (child : OTerm alpha) : Formula alpha :=
  if own then graph1 (OriginalCodeValidityGuard.check n) (suc z) child
  else graph2 InternalRawListRecursion.lookup (suc z) child f.previous

theorem transfer (own : Bool) (f : Frame n body Delta raw) (child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)))
    (ha : Nonempty (Derivation body Delta (accepted own f child))) :
    Nonempty (Derivation body Delta (accepted (!own) f child)) := by
  cases own with
  | false => exact ChildProof.toOwn n raw f.previous child f.prior hc ha
  | true => exact ChildProof.fromOwn n raw f.previous child f.prior hc ha

def C0 (o : Bool) (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 0) ⊔ eqn f.tag (numeral 3)
def C1 (o : Bool) (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 1) ⊓ accepted o f f.first
def C2 (o : Bool) (f : Frame n body Delta raw) : Formula alpha := (eqn f.tag (numeral 2) ⊔ eqn f.tag (numeral 7)) ⊓
  (accepted o f f.first ⊓ accepted o f f.second)
def C4 (o : Bool) (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 4) ⊓
  (graph1 (OriginalHeadDecoderValidity.check n) (suc z) f.head ⊓ accepted o f f.first)
def C5 (o : Bool) (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 5) ⊓
  ((graph1 (OriginalHeadDecoderValidity.check n) (suc z) f.head ⊓ accepted o f f.first) ⊓ accepted o f f.second)
def C6 (o : Bool) (f : Frame n body Delta raw) : Formula alpha := eqn f.tag (numeral 6) ⊓ eqn f.payload z

theorem at0 (o : Bool) (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C0 o f))) :
    Nonempty (Derivation body Delta (C0 (!o) f)) := by
  exact ha

theorem at1 (o : Bool) (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C1 o f))) :
    Nonempty (Derivation body Delta (C1 (!o) f)) := by
  have hc := OriginalCodeValidityCoherence.DescentProof.unary 1 (by decide) raw f.tag f.payload f.first
    f.pair (andLeft ha) f.firstGraph
  exact andIntro (andLeft ha) (transfer o f f.first hc (andRight ha))

theorem at2 (o : Bool) (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C2 o f))) :
    Nonempty (Derivation body Delta (C2 (!o) f)) := by
  have hc : Nonempty (Derivation body Delta
      (InternalLessThan.strictLess f.first raw ⊓ InternalLessThan.strictLess f.second raw)) := by
    apply orCases (andLeft ha)
    · exact OriginalCodeValidityCoherence.DescentProof.binary 2 (by decide) raw f.tag f.payload f.first f.second
        (f.withHyp _).pair ⟨Derivation.hypothesis List.mem_cons_self⟩ (f.withHyp _).firstGraph (f.withHyp _).secondGraph
    · exact OriginalCodeValidityCoherence.DescentProof.binary 7 (by decide) raw f.tag f.payload f.first f.second
        (f.withHyp _).pair ⟨Derivation.hypothesis List.mem_cons_self⟩ (f.withHyp _).firstGraph (f.withHyp _).secondGraph
  exact andIntro (andLeft ha) (andIntro (transfer o f f.first (andLeft hc) (andLeft (andRight ha))) (transfer o f f.second (andRight hc) (andRight (andRight ha))))

theorem at4 (o : Bool) (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C4 o f))) :
    Nonempty (Derivation body Delta (C4 (!o) f)) := by
  have hc := OriginalCodeValidityCoherence.DescentProof.unary 4 (by decide) raw f.tag f.payload f.first
    f.pair (andLeft ha) f.firstGraph
  exact andIntro (andLeft ha) (andIntro (andLeft (andRight ha)) (transfer o f f.first hc (andRight (andRight ha))))

theorem at5 (o : Bool) (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C5 o f))) :
    Nonempty (Derivation body Delta (C5 (!o) f)) := by
  have hc := OriginalCodeValidityCoherence.DescentProof.binary 5 (by decide) raw f.tag f.payload f.first f.second
    f.pair (andLeft ha) f.firstGraph f.secondGraph
  exact andIntro (andLeft ha) (andIntro (andIntro (andLeft (andLeft (andRight ha)))
    (transfer o f f.first (andLeft hc) (andRight (andLeft (andRight ha)))))
    (transfer o f f.second (andRight hc) (andRight (andRight ha))))

theorem at6 (o : Bool) (f : Frame n body Delta raw) (ha : Nonempty (Derivation body Delta (C6 o f))) :
    Nonempty (Derivation body Delta (C6 (!o) f)) := by
  exact ha

def R4 (o : Bool) (f : Frame n body Delta raw) : Formula alpha := C5 o f ⊔ C6 o f
def R3 (o : Bool) (f : Frame n body Delta raw) : Formula alpha := C4 o f ⊔ R4 o f
def R2 (o : Bool) (f : Frame n body Delta raw) : Formula alpha := C2 o f ⊔ R3 o f
def R1 (o : Bool) (f : Frame n body Delta raw) : Formula alpha := C1 o f ⊔ R2 o f
def all (o : Bool) (f : Frame n body Delta raw) : Formula alpha := C0 o f ⊔ R1 o f

theorem tail4 (o : Bool) (f : Frame n body Delta raw)
    (ha : Nonempty (Derivation body Delta (R4 o f))) :
    Nonempty (Derivation body Delta (R4 (!o) f)) := by
  apply orCases ha
  · exact ⟨InternalQuotientComparisonProof.orLeft (Classical.choice (at5 o (f.withHyp (C5 o f))
      ⟨Derivation.hypothesis List.mem_cons_self⟩))⟩
  · exact ⟨InternalQuotientComparisonProof.orRight (Classical.choice (at6 o (f.withHyp (C6 o f))
      ⟨Derivation.hypothesis List.mem_cons_self⟩))⟩

theorem tail3 (o : Bool) (f : Frame n body Delta raw)
    (ha : Nonempty (Derivation body Delta (R3 o f))) :
    Nonempty (Derivation body Delta (R3 (!o) f)) := by
  apply orCases ha
  · exact ⟨InternalQuotientComparisonProof.orLeft (Classical.choice (at4 o (f.withHyp (C4 o f))
      ⟨Derivation.hypothesis List.mem_cons_self⟩))⟩
  · exact ⟨InternalQuotientComparisonProof.orRight (Classical.choice (tail4 o (f.withHyp (R4 o f))
      ⟨Derivation.hypothesis List.mem_cons_self⟩))⟩

theorem tail2 (o : Bool) (f : Frame n body Delta raw)
    (ha : Nonempty (Derivation body Delta (R2 o f))) :
    Nonempty (Derivation body Delta (R2 (!o) f)) := by
  apply orCases ha
  · exact ⟨InternalQuotientComparisonProof.orLeft (Classical.choice (at2 o (f.withHyp (C2 o f))
      ⟨Derivation.hypothesis List.mem_cons_self⟩))⟩
  · exact ⟨InternalQuotientComparisonProof.orRight (Classical.choice (tail3 o (f.withHyp (R3 o f))
      ⟨Derivation.hypothesis List.mem_cons_self⟩))⟩

theorem tail1 (o : Bool) (f : Frame n body Delta raw)
    (ha : Nonempty (Derivation body Delta (R1 o f))) :
    Nonempty (Derivation body Delta (R1 (!o) f)) := by
  apply orCases ha
  · exact ⟨InternalQuotientComparisonProof.orLeft (Classical.choice (at1 o (f.withHyp (C1 o f))
      ⟨Derivation.hypothesis List.mem_cons_self⟩))⟩
  · exact ⟨InternalQuotientComparisonProof.orRight (Classical.choice (tail2 o (f.withHyp (R2 o f))
      ⟨Derivation.hypothesis List.mem_cons_self⟩))⟩

theorem tail0 (o : Bool) (f : Frame n body Delta raw)
    (ha : Nonempty (Derivation body Delta (all o f))) :
    Nonempty (Derivation body Delta (all (!o) f)) := by
  apply orCases ha
  · exact ⟨InternalQuotientComparisonProof.orLeft (Classical.choice (at0 o (f.withHyp (C0 o f))
      ⟨Derivation.hypothesis List.mem_cons_self⟩))⟩
  · exact ⟨InternalQuotientComparisonProof.orRight (Classical.choice (tail1 o (f.withHyp (R1 o f))
      ⟨Derivation.hypothesis List.mem_cons_self⟩))⟩

theorem toOwn (f : Frame n body Delta raw)
    (ha : Nonempty (Derivation body Delta (OriginalCodeDecoderStep.Targets.allowed n f.previous f.tag f.payload f.first f.second f.head))) :
    Nonempty (Derivation body Delta (Targets.allowed n f.tag f.payload f.first f.second f.head)) :=
  tail0 false f ha

theorem fromOwn (f : Frame n body Delta raw)
    (ha : Nonempty (Derivation body Delta (Targets.allowed n f.tag f.payload f.first f.second f.head))) :
    Nonempty (Derivation body Delta (OriginalCodeDecoderStep.Targets.allowed n f.previous f.tag f.payload f.first f.second f.head)) :=
  tail0 true f ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.ClauseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.ClauseProof
