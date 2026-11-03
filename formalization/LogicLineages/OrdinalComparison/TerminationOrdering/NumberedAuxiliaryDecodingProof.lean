module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecodingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecodingProof
open Source Source.SourceMarkedSyntax Source.SourceTypedPorts NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding

theorem headRoundTrip {Symbol : Type} (f : Head Symbol) : decodeHead (headCode f)=f := by cases f <;> rfl
theorem headSound {Symbol : Type} (f : HeadCode Symbol) : headCode (decodeHead f)=f := by cases f <;> rfl

theorem variableRoundTrip {Gamma : List Ty} {tau : Ty} (v : Variable Gamma tau) :
    decodeVariable Gamma tau (variableIndex v)=some v := by
  induction v with
  | here => simp [decodeVariable,variableIndex]
  | there v ih => simp [decodeVariable,variableIndex,ih]

theorem variableSound (Gamma : List Ty) (tau : Ty) (i : Nat) (v : Variable Gamma tau)
    (h : decodeVariable Gamma tau i=some v) : variableIndex v=i := by
  induction Gamma generalizing i with
  | nil => simp [decodeVariable] at h
  | cons sigma Gamma ih =>
    cases i with
    | zero =>
      simp only [decodeVariable] at h
      split at h
      next he => cases he; cases h; rfl
      next => contradiction
    | succ i =>
      simp only [decodeVariable,Option.map_eq_some_iff] at h
      obtain ⟨w,hw,hv⟩ := h
      cases hv
      exact congrArg Nat.succ (ih i w hw)

theorem termRoundTrip : NumberedAuxiliaryDecodingTargets.ActualTermRoundTrip := by
  intro Symbol arity Gamma tau q
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types args => decodeArguments arity Gamma types (argumentsCode args)=some args)
  case ordinary f args ih =>
    simp only [termCode]
    cases f <;> simp_all [decodeTerm,headCode,decodeHead]
  case numbered k f tau args types extras ihb ihe =>
    simp only [termCode]
    cases f <;> simp_all [decodeTerm,headCode,decodeHead]
  all_goals simp_all [termCode,argumentsCode,decodeTerm,decodeArguments,headRoundTrip,variableRoundTrip]

theorem argumentsRoundTrip : NumberedAuxiliaryDecodingTargets.ActualArgumentsRoundTrip := by
  intro Symbol arity Gamma types args
  induction types with
  | nil => cases args; rfl
  | cons sigma types ih =>
    cases args with
    | cons q rest => simp [argumentsCode,decodeArguments,termRoundTrip Symbol arity Gamma sigma q,ih rest]

theorem decodeSound {Symbol : Type} (arity : Symbol → Nat) (c : Code Symbol) :
    (∀ Gamma tau (q : AuxTerm Symbol arity Gamma tau),decodeTerm arity Gamma tau c=some q → termCode q=c) ∧
    (∀ Gamma types (args : AuxArguments Symbol arity Gamma types),decodeArguments arity Gamma types c=some args → argumentsCode args=c) := by
  induction c with
  | var i =>
    constructor
    · intro Gamma tau q h
      simp only [decodeTerm,Option.map_eq_some_iff] at h
      obtain ⟨v,hv,hq⟩ := h
      cases hq
      exact congrArg Code.var (variableSound Gamma tau i v hv)
    · intro Gamma types args h; simp [decodeArguments] at h
  | lam sigma body ih =>
    constructor
    · intro Gamma tau q h
      cases tau with
      | ground => simp [decodeTerm] at h
      | arrow domain result =>
        simp only [decodeTerm] at h
        split at h
        next he =>
          cases he
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨b,hb,hq⟩ := h
          cases hq
          exact congrArg (Code.lam sigma) (ih.1 _ _ b hb)
        next => contradiction
    · intro Gamma types args h; simp [decodeArguments] at h
  | app sigma function argument ihf iha =>
    constructor
    · intro Gamma tau q h
      cases hf : decodeTerm arity Gamma (.arrow sigma tau) function with
      | none => simp [decodeTerm,hf] at h
      | some f =>
        cases ha : decodeTerm arity Gamma sigma argument with
        | none => simp [decodeTerm,hf,ha] at h
        | some a =>
          simp [decodeTerm,hf,ha] at h
          cases h
          exact congrArg₂ (Code.app sigma) (ihf.1 _ _ f hf) (iha.1 _ _ a ha)
    · intro Gamma types args h; simp [decodeArguments] at h
  | bottom result =>
    constructor
    · intro Gamma tau q h
      simp only [decodeTerm] at h
      split at h
      next he => cases he; cases h; rfl
      next => contradiction
    · intro Gamma types args h; simp [decodeArguments] at h
  | ordinary head base ih =>
    constructor
    · intro Gamma tau q h
      simp only [decodeTerm] at h
      split at h
      next he =>
        cases he
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨args,ha,hq⟩ := h
        cases hq
        simp only [termCode,headSound]
        exact congrArg (Code.ordinary head) (ih.2 _ _ args ha)
      next => contradiction
    · intro Gamma types args h; simp [decodeArguments] at h
  | numbered k head result base types extras ihb ihe =>
    constructor
    · intro Gamma tau q h
      simp only [decodeTerm] at h
      split at h
      next he =>
        cases he
        cases ha : decodeArguments arity Gamma (headArguments arity (decodeHead head)) base with
        | none => simp [ha] at h
        | some args =>
          cases he : decodeArguments arity Gamma types extras with
          | none => simp [ha,he] at h
          | some extraArgs =>
            simp [ha,he] at h
            cases h
            simp only [termCode,headSound]
            exact congrArg₂ (fun b e => Code.numbered k head result b types e)
              (ihb.2 _ _ args ha) (ihe.2 _ _ extraArgs he)
      next => contradiction
    · intro Gamma ts args h; simp [decodeArguments] at h
  | argumentsNil =>
    constructor
    · intro Gamma tau q h; simp [decodeTerm] at h
    · intro Gamma types args h
      cases types with
      | nil => cases h; rfl
      | cons => simp [decodeArguments] at h
  | argumentsCons sigma q rest ihq ihr =>
    constructor
    · intro Gamma tau value h; simp [decodeTerm] at h
    · intro Gamma types args h
      cases types with
      | nil => simp [decodeArguments] at h
      | cons domain tail =>
        simp only [decodeArguments] at h
        split at h
        next he =>
          cases he
          cases hv : decodeTerm arity Gamma sigma q with
          | none => simp [hv] at h
          | some value =>
            cases hs : decodeArguments arity Gamma tail rest with
            | none => simp [hv,hs] at h
            | some values =>
              simp [hv,hs] at h
              cases h
              exact congrArg₂ (Code.argumentsCons sigma) (ihq.1 _ _ value hv) (ihr.2 _ _ values hs)
        next => contradiction

theorem termDecodeSound : NumberedAuxiliaryDecodingTargets.ActualTermDecodeSound := by
  intro Symbol arity Gamma tau c q h
  exact (decodeSound arity c).1 Gamma tau q h

theorem argumentsDecodeSound : NumberedAuxiliaryDecodingTargets.ActualArgumentsDecodeSound := by
  intro Symbol arity Gamma types c args h
  exact (decodeSound arity c).2 Gamma types args h

theorem packedRoundTrip : NumberedAuxiliaryDecodingTargets.ActualPackedRoundTrip := by
  intro Symbol arity Gamma q
  simp [decodePacked,packedCode,termRoundTrip Symbol arity Gamma q.1 q.2]

theorem candidateCoverage : NumberedAuxiliaryDecodingTargets.ActualCandidateCoverage := by
  intro Symbol inst arity symbols S hc Gamma q r hg hp
  apply List.mem_filterMap.mpr
  exact ⟨packedCode r,NumberedAuxiliaryEnumerationProof.primaryClassCoverage Symbol inst arity symbols S hc Gamma q r hg hp,
    packedRoundTrip Symbol arity Gamma r⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryDecodingProof
