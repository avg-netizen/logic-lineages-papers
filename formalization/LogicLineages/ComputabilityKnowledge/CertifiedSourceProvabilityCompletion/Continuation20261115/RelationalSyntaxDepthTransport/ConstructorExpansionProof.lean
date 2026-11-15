module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorStepTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorExpansionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261112.Fuel
open HistoryRuleSuffix LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof
open LiteralSyntaxStep LiteralSyntaxStep.ExpansionSupportProof ConstructorStepTargets

theorem term0 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 0 binder ::ᵥ Term.numeral 0 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.term 0)))) := by
 let args := taskCall ptag 0 binder ::ᵥ Term.numeral 0 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 0) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 0) := projection p G args 1
 have hout := successValue p G args _ _ (singletonValue p G args ctag hc _ _ (taskValue p G args ptag hp 2 context binder hn))
 apply whenEq p G args _ _ _ 0 _ hk
 exact whenEq p G args _ _ _ 0 _ ht hout

theorem term1 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 0 binder ::ᵥ Term.numeral 1 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.term 1)))) := by
 let args := taskCall ptag 0 binder ::ᵥ Term.numeral 1 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 0) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 1) := projection p G args 1
 have hout := constantValue p G args 1
 apply whenEq p G args _ _ _ 0 _ hk
 apply whenNe p G args _ _ _ 1 0 _ (by decide) ht
 exact whenEq p G args _ _ _ 1 _ ht hout

theorem term2 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 0 binder ::ᵥ Term.numeral 2 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.term 2)))) := by
 let args := taskCall ptag 0 binder ::ᵥ Term.numeral 2 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 0) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 2) := projection p G args 1
 have hout := successValue p G args _ _ (singletonValue p G args ctag hc _ _ (taskValue p G args ptag hp 0 context binder hn))
 apply whenEq p G args _ _ _ 0 _ hk
 apply whenNe p G args _ _ _ 2 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 2 1 _ (by decide) ht
 exact whenEq p G args _ _ _ 2 _ ht hout

theorem term3 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 0 binder ::ᵥ Term.numeral 3 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.term 3)))) := by
 let args := taskCall ptag 0 binder ::ᵥ Term.numeral 3 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 0) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 3) := projection p G args 1
 have hout := successValue p G args _ _ (doubleValue p G args ctag hc _ _ (taskValue p G args ptag hp 0 context binder hn))
 apply whenEq p G args _ _ _ 0 _ hk
 apply whenNe p G args _ _ _ 3 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 3 1 _ (by decide) ht
 apply whenNe p G args _ _ _ 3 2 _ (by decide) ht
 apply whenNe p G args _ _ _ 3 5 _ (by decide) ht
 exact whenEq p G args _ _ _ 3 _ ht hout

theorem term4 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 0 binder ::ᵥ Term.numeral 4 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.term 4)))) := by
 let args := taskCall ptag 0 binder ::ᵥ Term.numeral 4 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 0) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 4) := projection p G args 1
 have hout := successValue p G args _ _ (doubleValue p G args ctag hc _ _ (taskValue p G args ptag hp 0 context binder hn))
 apply whenEq p G args _ _ _ 0 _ hk
 apply whenNe p G args _ _ _ 4 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 4 1 _ (by decide) ht
 apply whenNe p G args _ _ _ 4 2 _ (by decide) ht
 apply whenNe p G args _ _ _ 4 5 _ (by decide) ht
 apply whenNe p G args _ _ _ 4 3 _ (by decide) ht
 exact whenEq p G args _ _ _ 4 _ ht hout

theorem term5 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 0 binder ::ᵥ Term.numeral 5 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.term 5)))) := by
 let args := taskCall ptag 0 binder ::ᵥ Term.numeral 5 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 0) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 5) := projection p G args 1
 have hout := successValue p G args _ _ (singletonValue p G args ctag hc _ _ (taskValue p G args ptag hp 0 context binder hn))
 apply whenEq p G args _ _ _ 0 _ hk
 apply whenNe p G args _ _ _ 5 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 5 1 _ (by decide) ht
 apply whenNe p G args _ _ _ 5 2 _ (by decide) ht
 exact whenEq p G args _ _ _ 5 _ ht hout

theorem formula0 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral 0 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.formula 0)))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 0 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 1) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 0) := projection p G args 1
 have hout := successValue p G args _ _ (doubleValue p G args ctag hc _ _ (taskValue p G args ptag hp 0 context binder hn))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 exact whenEq p G args _ _ _ 0 _ ht hout

theorem formula1 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral 1 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.formula 1)))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 1 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 1) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 1) := projection p G args 1
 have hout := successValue p G args _ _ (singletonValue p G args ctag hc _ _ (taskValue p G args ptag hp 0 context binder hn))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ 1 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 1 4 _ (by decide) ht
 exact whenEq p G args _ _ _ 1 _ ht hout

theorem formula2 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral 2 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.formula 2)))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 2 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 1) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 2) := projection p G args 1
 have hout := successValue p G args _ _ (singletonValue p G args ctag hc _ _ (taskValue p G args ptag hp 0 context binder hn))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ 2 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 2 4 _ (by decide) ht
 apply whenNe p G args _ _ _ 2 1 _ (by decide) ht
 exact whenEq p G args _ _ _ 2 _ ht hout

theorem formula3 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral 3 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.formula 3)))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 3 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 1) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 3) := projection p G args 1
 have hout := successValue p G args _ _ (singletonValue p G args ctag hc _ _ (taskValue p G args ptag hp 0 context binder hn))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ 3 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 3 4 _ (by decide) ht
 apply whenNe p G args _ _ _ 3 1 _ (by decide) ht
 apply whenNe p G args _ _ _ 3 2 _ (by decide) ht
 exact whenEq p G args _ _ _ 3 _ ht hout

theorem formula4 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral 4 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.formula 4)))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 4 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 1) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 4) := projection p G args 1
 have hout := successValue p G args _ _ (doubleValue p G args ctag hc _ _ (taskValue p G args ptag hp 0 context binder hn))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ 4 0 _ (by decide) ht
 exact whenEq p G args _ _ _ 4 _ ht hout

theorem formula5 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral 5 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.formula 5)))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 5 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 1) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 5) := projection p G args 1
 have hout := successValue p G args _ _ (singletonValue p G args ctag hc _ _ (taskValue p G args ptag hp 0 context binder hn))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ 5 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 5 4 _ (by decide) ht
 apply whenNe p G args _ _ _ 5 1 _ (by decide) ht
 apply whenNe p G args _ _ _ 5 2 _ (by decide) ht
 apply whenNe p G args _ _ _ 5 3 _ (by decide) ht
 exact whenEq p G args _ _ _ 5 _ ht hout

theorem formula6 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral 6 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.formula 6)))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 6 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 1) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 6) := projection p G args 1
 have hout := successValue p G args _ _ (singletonValue p G args ctag hc _ _ (taskValue p G args ptag hp 1 context binder hn))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ 6 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 6 4 _ (by decide) ht
 apply whenNe p G args _ _ _ 6 1 _ (by decide) ht
 apply whenNe p G args _ _ _ 6 2 _ (by decide) ht
 apply whenNe p G args _ _ _ 6 3 _ (by decide) ht
 apply whenNe p G args _ _ _ 6 5 _ (by decide) ht
 exact whenEq p G args _ _ _ 6 _ ht hout

theorem formula7 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral 7 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.formula 7)))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 7 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 1) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 7) := projection p G args 1
 have hout := successValue p G args _ _ (doubleValue p G args ctag hc _ _ (taskValue p G args ptag hp 1 context binder hn))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ 7 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 7 4 _ (by decide) ht
 apply whenNe p G args _ _ _ 7 1 _ (by decide) ht
 apply whenNe p G args _ _ _ 7 2 _ (by decide) ht
 apply whenNe p G args _ _ _ 7 3 _ (by decide) ht
 apply whenNe p G args _ _ _ 7 5 _ (by decide) ht
 apply whenNe p G args _ _ _ 7 6 _ (by decide) ht
 exact whenEq p G args _ _ _ 7 _ ht hout

theorem formula8 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral 8 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.formula 8)))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 8 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 1) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 8) := projection p G args 1
 have hout := successValue p G args _ _ (doubleValue p G args ctag hc _ _ (taskValue p G args ptag hp 1 context binder hn))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ 8 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 8 4 _ (by decide) ht
 apply whenNe p G args _ _ _ 8 1 _ (by decide) ht
 apply whenNe p G args _ _ _ 8 2 _ (by decide) ht
 apply whenNe p G args _ _ _ 8 3 _ (by decide) ht
 apply whenNe p G args _ _ _ 8 5 _ (by decide) ht
 apply whenNe p G args _ _ _ 8 6 _ (by decide) ht
 apply whenNe p G args _ _ _ 8 7 _ (by decide) ht
 exact whenEq p G args _ _ _ 8 _ ht hout

theorem formula9 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral 9 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.formula 9)))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 9 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 1) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 9) := projection p G args 1
 have hout := successValue p G args _ _ (doubleValue p G args ctag hc _ _ (taskValue p G args ptag hp 1 context binder hn))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ 9 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 9 4 _ (by decide) ht
 apply whenNe p G args _ _ _ 9 1 _ (by decide) ht
 apply whenNe p G args _ _ _ 9 2 _ (by decide) ht
 apply whenNe p G args _ _ _ 9 3 _ (by decide) ht
 apply whenNe p G args _ _ _ 9 5 _ (by decide) ht
 apply whenNe p G args _ _ _ 9 6 _ (by decide) ht
 apply whenNe p G args _ _ _ 9 7 _ (by decide) ht
 apply whenNe p G args _ _ _ 9 8 _ (by decide) ht
 exact whenEq p G args _ _ _ 9 _ ht hout

theorem formula10 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral 10 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.formula 10)))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 10 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 1) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 10) := projection p G args 1
 have hsucc := unary p G args .succ context binder (.succ binder) hn (StepSupportProof.successor p G binder)
 have hout := successValue p G args _ _ (singletonValue p G args ctag hc _ _ (taskValue p G args ptag hp 1 (applyOne .succ context) (.succ binder) hsucc))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ 10 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 10 4 _ (by decide) ht
 apply whenNe p G args _ _ _ 10 1 _ (by decide) ht
 apply whenNe p G args _ _ _ 10 2 _ (by decide) ht
 apply whenNe p G args _ _ _ 10 3 _ (by decide) ht
 apply whenNe p G args _ _ _ 10 5 _ (by decide) ht
 apply whenNe p G args _ _ _ 10 6 _ (by decide) ht
 apply whenNe p G args _ _ _ 10 7 _ (by decide) ht
 apply whenNe p G args _ _ _ 10 8 _ (by decide) ht
 apply whenNe p G args _ _ _ 10 9 _ (by decide) ht
 exact whenEq p G args _ _ _ 10 _ ht hout

theorem formula11 {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) :
 Computes p G expandCode (taskCall ptag 1 binder ::ᵥ Term.numeral 11 ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder (.formula 11)))) := by
 let args := taskCall ptag 1 binder ::ᵥ Term.numeral 11 ::ᵥ nil
 have hk : Computes p G LiteralSyntaxStep.kind args (Term.numeral 1) :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp false _ _)
 have hn : Computes p G context args binder :=
  unary p G args _ _ _ _ (projection p G args 0) (decoder p G ptag hp true _ _)
 have ht : Computes p G (.projection 1) args (Term.numeral 11) := projection p G args 1
 have hsucc := unary p G args .succ context binder (.succ binder) hn (StepSupportProof.successor p G binder)
 have hout := successValue p G args _ _ (singletonValue p G args ctag hc _ _ (taskValue p G args ptag hp 1 (applyOne .succ context) (.succ binder) hsucc))
 apply whenNe p G args _ _ _ 1 0 _ (by decide) hk
 apply whenEq p G args _ _ _ 1 _ hk
 apply whenNe p G args _ _ _ 11 0 _ (by decide) ht
 apply whenNe p G args _ _ _ 11 4 _ (by decide) ht
 apply whenNe p G args _ _ _ 11 1 _ (by decide) ht
 apply whenNe p G args _ _ _ 11 2 _ (by decide) ht
 apply whenNe p G args _ _ _ 11 3 _ (by decide) ht
 apply whenNe p G args _ _ _ 11 5 _ (by decide) ht
 apply whenNe p G args _ _ _ 11 6 _ (by decide) ht
 apply whenNe p G args _ _ _ 11 7 _ (by decide) ht
 apply whenNe p G args _ _ _ 11 8 _ (by decide) ht
 apply whenNe p G args _ _ _ 11 9 _ (by decide) ht
 apply whenNe p G args _ _ _ 11 10 _ (by decide) ht
 exact whenEq p G args _ _ _ 11 _ ht hout

/-- All eighteen original constructor expansion branches, with arbitrary runtime
bound and installed registry addresses. This does not cover malformed tokens. -/
theorem constructorAt {n ctx : Nat} (p : Program n) (G : List (Formula ctx)) (ptag ctag : Nat)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (binder : Term ctx) (ctor : Constructor) :
 Computes p G expandCode (taskCall ptag (ConstructorStepTargets.kind ctor) binder ::ᵥ
  Term.numeral (token ctor) ::ᵥ nil)
  (.succ (FinitePrefixTargets.prefixTerm ctag (tasks ptag binder ctor))) := by
 cases ctor with
 | term i =>
  have hi := i.isLt
  have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5
  · have he : i = (0 : Fin 6) := Fin.ext h0
    subst i
    exact term0 p G ptag ctag hp hc binder
  · have he : i = (1 : Fin 6) := Fin.ext h1
    subst i
    exact term1 p G ptag ctag hp hc binder
  · have he : i = (2 : Fin 6) := Fin.ext h2
    subst i
    exact term2 p G ptag ctag hp hc binder
  · have he : i = (3 : Fin 6) := Fin.ext h3
    subst i
    exact term3 p G ptag ctag hp hc binder
  · have he : i = (4 : Fin 6) := Fin.ext h4
    subst i
    exact term4 p G ptag ctag hp hc binder
  · have he : i = (5 : Fin 6) := Fin.ext h5
    subst i
    exact term5 p G ptag ctag hp hc binder
 | formula i =>
  have hi := i.isLt
  have hcases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · have he : i = (0 : Fin 12) := Fin.ext h0
    subst i
    exact formula0 p G ptag ctag hp hc binder
  · have he : i = (1 : Fin 12) := Fin.ext h1
    subst i
    exact formula1 p G ptag ctag hp hc binder
  · have he : i = (2 : Fin 12) := Fin.ext h2
    subst i
    exact formula2 p G ptag ctag hp hc binder
  · have he : i = (3 : Fin 12) := Fin.ext h3
    subst i
    exact formula3 p G ptag ctag hp hc binder
  · have he : i = (4 : Fin 12) := Fin.ext h4
    subst i
    exact formula4 p G ptag ctag hp hc binder
  · have he : i = (5 : Fin 12) := Fin.ext h5
    subst i
    exact formula5 p G ptag ctag hp hc binder
  · have he : i = (6 : Fin 12) := Fin.ext h6
    subst i
    exact formula6 p G ptag ctag hp hc binder
  · have he : i = (7 : Fin 12) := Fin.ext h7
    subst i
    exact formula7 p G ptag ctag hp hc binder
  · have he : i = (8 : Fin 12) := Fin.ext h8
    subst i
    exact formula8 p G ptag ctag hp hc binder
  · have he : i = (9 : Fin 12) := Fin.ext h9
    subst i
    exact formula9 p G ptag ctag hp hc binder
  · have he : i = (10 : Fin 12) := Fin.ext h10
    subst i
    exact formula10 p G ptag ctag hp hc binder
  · have he : i = (11 : Fin 12) := Fin.ext h11
    subst i
    exact formula11 p G ptag ctag hp hc binder
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorExpansionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ConstructorExpansionProof
