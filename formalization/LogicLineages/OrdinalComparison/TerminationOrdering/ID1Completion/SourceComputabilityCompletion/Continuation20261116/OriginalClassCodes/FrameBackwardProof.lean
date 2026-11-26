module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.FrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairIntroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.FrameBackwardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalApplicationStepPeelSupportProof (andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {alpha : Type} {n : Nat} {arity : Fin n → Nat} {H : Program 1}
variable {body : Positive (Fin 1)} {Delta : List (Formula alpha)} {seed param candidate : OTerm alpha}

def tailQueries (n : Nat) (arity : Fin n → Nat) : Fin 5 → Program 2 :=
  ![node n,parameter n arity,InputProof.metadataMiddle n arity,InputProof.metadataTail n,enumerated n arity]

def ofMeaning (xs : Fin 9 → OTerm alpha) (ys : Fin 5 → OTerm alpha)
    (h : Nonempty (Derivation body Delta (Meaning.observations n arity H seed param candidate xs)))
    (ht : ∀ i, Nonempty (Derivation body Delta (graph2 (tailQueries n arity i) (ys i) seed param))) :
    Frame n arity H body Delta seed param where
  values := ![xs 1,xs 2,xs 3,xs 4,xs 5,xs 6,xs 7,xs 8,ys 0,ys 1,ys 2,ys 3,ys 4]
  graph := by
    intro i
    fin_cases i
    · exact MeaningPartsProof.rootPart n arity H seed param candidate xs h
    · exact MeaningPartsProof.typesPart n arity H seed param candidate xs h
    · exact MeaningPartsProof.headsPart n arity H seed param candidate xs h
    · exact MeaningPartsProof.sizePart n arity H seed param candidate xs h
    · exact MeaningPartsProof.labelsPart n arity H seed param candidate xs h
    · exact MeaningPartsProof.boundPart n arity H seed param candidate xs h
    · exact MeaningPartsProof.fuelPart n arity H seed param candidate xs h
    · exact MeaningPartsProof.admissionPart n arity H seed param candidate xs h
    · exact ht 0
    · exact ht 1
    · exact ht 2
    · exact ht 3
    · exact ht 4

theorem atValues (xs : Fin 9 → OTerm alpha) (ys : Fin 5 → OTerm alpha) (out : OTerm alpha)
    (h : Nonempty (Derivation body Delta (Meaning.observations n arity H seed param candidate xs)))
    (ht : ∀ i, Nonempty (Derivation body Delta (graph2 (tailQueries n arity i) (ys i) seed param)))
    (hc : Nonempty (Derivation body Delta (graph2 (classCodes n arity H) out seed param))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out candidate)) := by
  let f := ofMeaning xs ys h ht
  have hn := MeaningPartsProof.nonzeroPart n arity H seed param candidate xs h
  have hp := MeaningPartsProof.pairPart n arity H seed param candidate xs h
  have hf := MeaningPartsProof.fieldsPart n arity H seed param candidate xs h
  have hd := MeaningPartsProof.depthPart n arity H seed param candidate xs h
  have hm := (FrameProof.characterize f (xs 0)).mpr (andIntro hf hd)
  exact PairIntroProof.introduce (f.values 12) (f.values 0) out candidate z (xs 0)
    (FrameProof.mapped f out hn hc) hm hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.FrameBackwardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.FrameBackwardProof
