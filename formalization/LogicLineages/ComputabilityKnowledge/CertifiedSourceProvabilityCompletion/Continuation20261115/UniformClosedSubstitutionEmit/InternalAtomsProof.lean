module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.InternalAtomsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep.StepSupportProof SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix
abbrev activeInput {ctx : Nat} (ptag ctag : Nat) (kind bound rest token raw : Term ctx) : List.Vector (Term ctx) 3 :=
 stateValue ptag ctag kind bound rest ::ᵥ token ::ᵥ raw ::ᵥ nil
theorem singleton {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ctag
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (state token raw : Term ctx) :
 Computes p G singletonCode (state ::ᵥ token ::ᵥ raw ::ᵥ nil) (singletonValue ctag token) :=
 binary p G _ HistoryCodec.cons (.projection 1) (constant 3 0) token .zero _
  (projection p G _ 1) (constantValue p G _ 0) (copies p G HistoryCodec.cons ctag hc _)
theorem variableCodeValue {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ctag
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (state token raw : Term ctx) :
 Computes p G variableCode (state ::ᵥ token ::ᵥ raw ::ᵥ nil) (variableValue ctag token) :=
 binary p G _ HistoryCodec.cons (constant 3 0) singletonCode .zero (singletonValue ctag token) _
  (constantValue p G _ 0) (singleton p G ctag hc state token raw) (copies p G HistoryCodec.cons ctag hc _)
theorem stack {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag ctag (kind bound rest token raw : Term ctx) :
 Computes p G stackCode (activeInput ptag ctag kind bound rest token raw)
  (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag kind bound) rest) :=
 unary p G _ HistoryCodec.predecessor (.projection 0) _ _ (projection p G _ 0) (predecessor p G _)
theorem task {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag ctag
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (kind bound rest token raw : Term ctx) :
 Computes p G taskCode (activeInput ptag ctag kind bound rest token raw) (HistoryKernel.pairCall ptag kind bound) :=
 unary p G _ HistoryLookup.head stackCode _ _ (stack p G ptag ctag kind bound rest token raw)
  (headCons p G ctag hc _ rest)
theorem kind {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag ctag
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (k bound rest token raw : Term ctx) :
 Computes p G kindCode (activeInput ptag ctag k bound rest token raw) k :=
 unary p G _ (HistoryDecoder.decoder false) taskCode _ _ (task p G ptag ctag hc k bound rest token raw)
  (decoder p G ptag hp false k bound)
theorem bound {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag ctag
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (k b rest token raw : Term ctx) :
 Computes p G boundCode (activeInput ptag ctag k b rest token raw) b :=
 unary p G _ (HistoryDecoder.decoder true) taskCode _ _ (task p G ptag ctag hc k b rest token raw)
  (decoder p G ptag hp true k b)
theorem successorDepth {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag ctag
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (k depth rest token raw : Term ctx) :
 Computes p G depthCode (activeInput ptag ctag k (.succ depth) rest token raw) depth :=
 unary p G _ HistoryCodec.predecessor boundCode _ _ (bound p G ptag ctag hp hc k (.succ depth) rest token raw)
  (predecessor p G depth)
/-- Original NONE/SOME[] guards are discharged using actual cons positivity. -/
theorem enterActive {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) ptag ctag
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (kind bound rest token raw value : Term ctx)
 (ha : Computes p G activeCode (activeInput ptag ctag kind bound rest token raw) value) :
 Computes p G emitCode (activeInput ptag ctag kind bound rest token raw) value := by
 let row := HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag kind bound) rest
 let pairTag := ctag + argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 let pairValue := call pairTag (HistoryKernel.pairCall ptag kind bound ::ᵥ rest ::ᵥ nil)
 obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx (HistoryKernel.pairCall ptag kind bound) rest
 have hstack := changeValue p G stackCode _ row (.succ pairValue)
  (stack p G ptag ctag kind bound rest token raw) (.base hcons)
 exact choosePositive p G _ (.projection 0) singletonCode _ row value (projection p G _ 0)
  (choosePositive p G _ stackCode singletonCode activeCode pairValue value hstack ha)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.InternalAtomsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.InternalAtomsProof
