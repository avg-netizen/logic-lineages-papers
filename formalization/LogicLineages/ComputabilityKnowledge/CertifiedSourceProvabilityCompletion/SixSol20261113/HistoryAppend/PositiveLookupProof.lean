module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.LookupShiftProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.PositiveLookupProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph TableEquationsProof TableLookupProof AppendEquationsProof ValueEquationsProof PositiveProof

theorem lookupZeroPositive {n ctx : Nat} (p : Program n) tag htag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryLookup.lookup⟩)
    (hh : (nodes p)[htag]? = some ⟨1,HistoryLookup.head⟩) (count : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryLookup.lookupCall tag .zero (.succ count)) (.succ (call htag (.succ count ::ᵥ nil))))) := by
  let dt := HistoryLookup.LookupProof.dropTag tag
  let rt := tag+1
  let rh := HistoryLookup.ReferenceProof.headTag rt
  have hd := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryLookup.reference (fun _ : Fin 1 => HistoryLookup.drop) ht 0
  have hr := SixSol20261112.Fuel.Equations.functionChild p tag HistoryLookup.reference (fun _ : Fin 1 => HistoryLookup.drop) ht
  have hs := SixSol20261112.Fuel.Equations.functionChild p rt HistoryCodec.select HistoryLookup.referenceArguments hr
  obtain ⟨hl⟩ := HistoryLookup.LookupProof.lookupEquation p tag ht .zero (.succ count)
  obtain ⟨hz⟩ := HistoryLookup.DropEquationsProof.dropZero p dt hd (.succ count)
  obtain ⟨he⟩ := HistoryLookup.ReferenceProof.referenceEquation p rt hr (.succ count)
  obtain ⟨hsel⟩ := HistoryCodec.PairProof.selectPositive p (rt+1) hs .zero (.succ (call rh (.succ count ::ᵥ nil))) count
  obtain ⟨hcopy⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p rh htag 1 HistoryLookup.head
    (HistoryLookup.ReferenceProof.headInstalled p rt hr) hh ctx (.succ count ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ hl (Logic.trans _ _ _ (HistoryLookup.DestructorProof.unaryCallCongruence rt _ _ hz)
    (Logic.trans _ _ _ he (Logic.trans _ _ _ hsel (Logic.unary (.succ (.var 0)) _ _ hcopy))))⟩

theorem zeroAppendPositive {n ctx : Nat} (p : Program n) atag ltag
    (ha : (nodes p)[atag]? = some ⟨2,append⟩)
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryLookup.lookup⟩) (count right : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryLookup.lookupCall ltag .zero (appendCall atag (.succ count) right))
        (HistoryLookup.lookupCall ltag .zero (.succ count)))) := by
  have hv := valueInstalled p (tableTag atag) (tableInstalled p atag ha)
  obtain ⟨hc,hh,ht,hd,href,hp⟩ := valueNodes p (valueAt atag) hv
  obtain ⟨he⟩ := appendPositive p atag ha count right
  obtain ⟨hz⟩ := HistoryLookup.LookupProof.internalLookupZeroCons n p ltag (outputConsTag atag) hl hc ctx
    (call (inputHeadTag atag) (.succ count ::ᵥ nil))
    (appendCall atag (call (inputTailTag atag) (.succ count ::ᵥ nil)) right)
  obtain ⟨hsource⟩ := lookupZeroPositive p ltag (inputHeadTag atag) hl hh count
  exact ⟨Logic.trans _ _ _ (lookupCodeCongruence ltag .zero _ _ he)
    (Logic.trans _ _ _ hz (Support.equalitySymmetry _ _ hsource))⟩

theorem successorAppendPositive {n ctx : Nat} (p : Program n) atag ltag
    (ha : (nodes p)[atag]? = some ⟨2,append⟩)
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryLookup.lookup⟩) (index count right : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryLookup.lookupCall ltag (.succ index) (appendCall atag (.succ count) right))
        (HistoryLookup.lookupCall ltag index (appendCall atag (call (inputTailTag atag) (.succ count ::ᵥ nil)) right)))) := by
  have hv := valueInstalled p (tableTag atag) (tableInstalled p atag ha)
  obtain ⟨hc,hh,ht,hd,href,hp⟩ := valueNodes p (valueAt atag) hv
  obtain ⟨he⟩ := appendPositive p atag ha count right
  obtain ⟨hs⟩ := HistoryLookup.LookupProof.internalLookupSuccessorCons n p ltag (outputConsTag atag) hl hc ctx index
    (call (inputHeadTag atag) (.succ count ::ᵥ nil))
    (appendCall atag (call (inputTailTag atag) (.succ count ::ᵥ nil)) right)
  exact ⟨Logic.trans _ _ _ (lookupCodeCongruence ltag (.succ index) _ _ he) hs⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.PositiveLookupProof
