import Mathlib
import Sostactic.Backend
import Sostactic.Polynomials

open Lean Meta Elab Tactic Parser

namespace Sostactic

-- UTILS

def ppString (e : Expr) : MetaM String := do
  return ((← ppExpr e).pretty.trimAscii).toString

def inferTypeString (text : String) : TacticM String := do
  let env ← getEnv
  match runParserCategory env `term text with
  | .error err => throwError "failed to parse goal term '{text}': {err}"
  | .ok stx =>
      let expr ← elabTerm stx none
      ppString (← inferType expr)

def typedBackendExpr (text typeText : String) : String :=
  s!"(({backendToLean text}) : {typeText})"

def weightedTermString (typeText : String) (term : SerializedWeightedSOSTerm) : String :=
  s!"({typedBackendExpr term.weight typeText}) * ({typedBackendExpr term.poly.expr typeText})^2"

def weightedSumString (typeText : String) (terms : List SerializedWeightedSOSTerm) : String :=
  match terms.map (weightedTermString typeText) with
  | [] => "0"
  | xs => " + ".intercalate xs

def parseTacticString (text : String) : TacticM Syntax := do
  let env ← getEnv
  match runParserCategory env `tactic text with
  | .ok stx => return stx
  | .error err => throwError "failed to parse tactic:\n{text}\n\n{err}"

def evalTacticString (text : String) : TacticM Unit := do
  evalTactic (← parseTacticString text)

def normalizeNonnegGoal : TacticM String := do
  let goal ← getMainGoal
  let target ← goal.getType
  let text ← ppString target
  -- 0 ≤ expr
  if text.startsWith "0 ≤" then
    return (text.drop "0 ≤".length).trimAscii.toString
  -- expr ≥ 0
  if text.endsWith "≥ 0" then
    let expr := (text.dropEnd "≥ 0".length).trimAscii.toString
    evalTacticString s!"suffices _h_sostactic : (0 : ℝ) ≤ {expr} by linarith"
    return expr
  -- a ≤ b
  match text.splitOn " ≤ " with
  | [lhs, rhs] =>
    let diff := s!"{rhs.trimAscii} - ({lhs.trimAscii})"
    evalTacticString s!"suffices _h_sostactic : (0 : ℝ) ≤ {diff} by linarith"
    return diff
  | _ =>
  -- a ≥ b
  match text.splitOn " ≥ " with
  | [lhs, rhs] =>
    let diff := s!"{lhs.trimAscii} - ({rhs.trimAscii})"
    evalTacticString s!"suffices _h_sostactic : (0 : ℝ) ≤ {diff} by linarith"
    return diff
  | _ =>
    throwError "expected a goal of the form '0 ≤ f', 'a ≤ b', or 'a ≥ b'"

def parseTacticSeqString (text : String) : TacticM (TSyntax `Lean.Parser.Tactic.tacticSeq) := do
  let env ← getEnv
  let p := Parser.andthenFn Parser.whitespace Lean.Parser.Tactic.tacticSeq.fn
  let ictx := Parser.mkInputContext text "<input>"
  let s := p.run ictx { env, options := {} } (Parser.getTokenTable env) (Parser.mkParserState text)
  if s.hasError then
    throwError "failed to parse tactic sequence:\n{text}\n\n{s.toErrorMsg ictx}"
  else if s.pos.atEnd text then
    pure ⟨s.stxStack.back⟩
  else
    let errMsg := (s.mkError "end of input").toErrorMsg ictx
    throwError "failed to parse tactic sequence:\n{text}\n\n{errMsg}"

def evalTacticSeqString (text : String) : TacticM Unit := do
  evalTactic (← parseTacticSeqString text)

def tryEvalTacticString (text : String) : TacticM Unit := do
  let saved ← Tactic.saveState
  let hbSaved ← IO.getNumHeartbeats
  let msgsSaved := (← getThe Core.State).messages
  try
    withOptions (fun opts => opts.set `maxHeartbeats (800000 : Nat)) do
      evalTacticString text
  catch _ =>
    saved.restore (restoreInfo := true)
    IO.setNumHeartbeats hbSaved
    modifyThe Core.State fun s => { s with messages := msgsSaved }

def trySolveHeadGoalWithTacticString (text : String) (maxHeartbeats? : Option Nat := none) : TacticM Unit := do
  let saved ← saveState
  let goals ← getGoals
  match goals with
  | [] => pure ()
  | g :: rest =>
      setGoals [g]
      try
        match maxHeartbeats? with
        | some n =>
            withOptions (fun opts => opts.set `maxHeartbeats n) do
              evalTacticString text
        | none =>
            evalTacticString text
        let remaining ← getGoals
        if remaining.isEmpty then
          setGoals rest
        else
          restoreState saved
      catch _ =>
        restoreState saved

def containsSubstr (text needle : String) : Bool :=
  (text.splitOn needle).length > 1

def realVarNamesForGoal (goalTarget : String) : TacticM (Array String) := do
  let mut names := #[]
  for localDecl in ← getLCtx do
    if localDecl.isImplementationDetail || localDecl.isAuxDecl then
      continue
    let typeText ← ppString localDecl.type
    if typeText == "ℝ" then
      let name := localDecl.userName.toString
      if containsSubstr goalTarget name then
        names := names.push name
  return names

def replaceVars (text : String) (varNames : Array String) (replacements : Array String) : String :=
  let withPlaceholders :=
    Id.run do
      let mut acc := text
      for h : i in [:varNames.size] do
        let name := varNames[i]
        let placeholder := s!"__SOSTACTIC_VAR_{i}__"
        acc := acc.replace name placeholder
      acc
  Id.run do
    let mut acc := withPlaceholders
    for h : i in [:replacements.size] do
      let placeholder := s!"__SOSTACTIC_VAR_{i}__"
      acc := acc.replace placeholder replacements[i]
    acc

def scalarBackendExpr (text : String) (varNames replacements : Array String) : String :=
  s!"(({replaceVars (backendToLean text) varNames replacements}) : ℝ)"

def scalarWeightedTermString (varNames replacements : Array String) (term : SerializedWeightedSOSTerm) : String :=
  s!"({scalarBackendExpr term.weight #[] #[]}) * ({scalarBackendExpr term.poly.expr varNames replacements})^2"

def scalarWeightedSumString (varNames replacements : Array String) (terms : List SerializedWeightedSOSTerm) : String :=
  match terms.map (scalarWeightedTermString varNames replacements) with
  | [] => "0"
  | xs => " + ".intercalate xs

def takeLeadingDigits (chars : List Char) : String × List Char :=
  let rec go (acc : List Char) (rest : List Char) : String × List Char :=
    match rest with
    | c :: cs =>
        if c.isDigit then
          go (c :: acc) cs
        else
          (String.ofList acc.reverse, rest)
    | [] => (String.ofList acc.reverse, [])
  go [] chars

partial def dropLeadingWhitespace : List Char → List Char
  | c :: cs =>
      if c.isWhitespace then
        dropLeadingWhitespace cs
      else
        c :: cs
  | [] => []

partial def normalizeRationalDivs (text : String) : String :=
  let rec go : List Char → String
    | '/' :: cs =>
        let (digits, rest) := takeLeadingDigits (dropLeadingWhitespace cs)
        if digits.isEmpty then
          "/" ++ go cs
        else
          s!" * (MvPolynomial.C (1 / {digits} : ℝ))" ++ go rest
    | c :: cs => String.singleton c ++ go cs
    | [] => ""
  go text.toList

def mvPolyTypeString (nvars : Nat) : String :=
  s!"MvPolynomial (Fin {nvars}) ℝ"

def mvPolyExprString (nvars : Nat) (varNames : Array String) (text : String) : String :=
  let replacements := ((List.range nvars).map fun i => s!"X{i}").toArray
  let body := normalizeRationalDivs <| replaceVars (backendToLean text) varNames replacements
  s!"(({body}) : {mvPolyTypeString nvars})"

def mvPolyWeightedTermString (nvars : Nat) (varNames : Array String) (term : SerializedWeightedSOSTerm) : String :=
  s!"(MvPolynomial.C ({backendToLean term.weight} : ℝ)) * ({mvPolyExprString nvars varNames term.poly.expr})^2"

def mvPolyWeightedSumString (nvars : Nat) (varNames : Array String) (terms : List SerializedWeightedSOSTerm) : String :=
  match terms.map (mvPolyWeightedTermString nvars varNames) with
  | [] => s!"((0 : ℝ) : {mvPolyTypeString nvars})"
  | xs => " + ".intercalate xs

def realTupleString (varNames : Array String) : String :=
  s!"![{", ".intercalate varNames.toList}]"

def xDefsString (nvars : Nat) : String :=
  String.intercalate "\n" <|
    (List.range nvars).map fun i =>
      s!"let X{i} : {mvPolyTypeString nvars} := MvPolynomial.X {i}"

def polyRefsString (names : List String) (nvars : Nat) : String :=
  let refs := names ++ (List.range nvars).map (fun i => s!"X{i}")
  String.intercalate ", " refs

def evalVarReplacements (nvars : Nat) : Array String :=
  ((List.range nvars).map fun i => s!"(v {i})").toArray

def finsuppMonomialString (nvars : Nat) (exponents : List Nat) : String :=
  let rec go (i : Nat) : List Nat → List String
    | [] => []
    | 0 :: es => go (i + 1) es
    | e :: es => s!"Finsupp.single ({i} : Fin {nvars}) {e}" :: go (i + 1) es
  let pieces := go 0 exponents
  match pieces with
  | [] => s!"(0 : Fin {nvars} →₀ ℕ)"
  | x :: xs => String.intercalate " + " (x :: xs)

-- PLAIN SOS

def runSosDecomp (denomDegreeBound : Nat := 0)
    (denomTemplate : Option String := none)
    (certFile : Option String := none) : TacticM Unit := do
  let goalTarget ← normalizeNonnegGoal
  let typeText ← inferTypeString goalTarget
  unless typeText == "ℝ" do
    throwError "plain sos_decomp currently supports only goals over ℝ"

  let result ← match certFile with
    | some path => (loadBackendResult path : MetaM BackendResult)
    | none => (runSosBackend goalTarget denomDegreeBound denomTemplate : MetaM BackendResult)
  if !result.success then
    match result.suggestion with
    | some s => throwError "sos backend failed to find a certificate.\n\nHint: {s}"
    | none => throwError "sos backend failed to find a certificate"

  let denPoly := result.exact_den_poly.getD { expr := "1" }
  if denPoly.expr != "1" then
    let exactNumSos := result.exact_num_sos.getD []
    let exactDenSos := result.exact_den_sos.getD []
    if exactNumSos.isEmpty || exactDenSos.isEmpty then
      throwError "backend returned a denominator certificate without numerator/denominator SOS data"
    let coeffWitness := result.exact_den_nonzero_coeff_witness
    let varNames ← realVarNamesForGoal goalTarget
    let nvars := varNames.size
    let P := mvPolyExprString nvars varNames goalTarget
    let D := mvPolyWeightedSumString nvars varNames exactDenSos
    let N := mvPolyWeightedSumString nvars varNames exactNumSos
    let actualPoint := realTupleString varNames
    let mulRefs := polyRefsString ["D", "P", "N"] nvars
    let xRefs := polyRefsString [] nvars
    for i in List.range nvars do
      evalTacticString s!"let X{i} : {mvPolyTypeString nvars} := MvPolynomial.X {i}"
    evalTacticString s!"let P : {mvPolyTypeString nvars} := {P}"
    evalTacticString s!"let D : {mvPolyTypeString nvars} := {D}"
    evalTacticString s!"let N : {mvPolyTypeString nvars} := {N}"
    evalTacticSeqString s!"suffices hP_nonneg : ∀ v : Fin {nvars} → ℝ, 0 ≤ MvPolynomial.eval v P by
  simpa [P, {xRefs}] using hP_nonneg {actualPoint}"
    evalTacticString s!"refine nonneg_of_mul_of_nonneg_polynomials D P N ?hD_ne ?hmul ?hD_nonneg ?hN_nonneg"
    match coeffWitness with
    | some w =>
        let monom := finsuppMonomialString nvars w.exponents
        tryEvalTacticString s!"case hD_ne => rw [MvPolynomial.ne_zero_iff]; refine ⟨{monom}, ?_⟩; dsimp [D, {xRefs}]; simp [MvPolynomial.C_mul_X_pow_eq_monomial, Finsupp.single_eq_single_iff]"
    | none =>
        pure ()
    tryEvalTacticString s!"case hmul => apply MvPolynomial.funext; intro v; simp [{mulRefs}]; ring_nf"
    tryEvalTacticString s!"case hD_nonneg => intro v; simp [D, {xRefs}]; positivity"
    tryEvalTacticString s!"case hN_nonneg => intro v; simp [N, {xRefs}]; positivity"
    return

  let exactSos := result.exact_sos.getD []
  let rhs := weightedSumString typeText exactSos
  evalTacticString s!"have sostactic_sos_identity : (({goalTarget}) : {typeText}) = {rhs} := by ring_nf"
  evalTacticString s!"rw [sostactic_sos_identity]"
  evalTacticString "positivity"

syntax (name := sosDecompTac) "sos_decomp" : tactic
syntax (name := sosDecompDegreeTac) "sos_decomp" "(" "degree" ":=" num ")" : tactic
syntax (name := sosDecompTemplateTac) "sos_decomp" "(" "degree" ":=" num ")" "(" "denom_template" ":=" str ")" : tactic
syntax (name := sosDecompCertTac) "sos_decomp" "(" "cert" ":=" str ")" : tactic

elab_rules : tactic
  | `(tactic| sos_decomp) => Lean.Elab.Tactic.focus do runSosDecomp
  | `(tactic| sos_decomp (degree := $d:num)) => Lean.Elab.Tactic.focus do runSosDecomp d.getNat
  | `(tactic| sos_decomp (degree := $d:num) (denom_template := $t:str)) =>
    Lean.Elab.Tactic.focus do runSosDecomp d.getNat (some t.getString)
  | `(tactic| sos_decomp (cert := $c:str)) =>
    Lean.Elab.Tactic.focus do runSosDecomp (certFile := some c.getString)

-- POSITIVSTELLENSATZ (PUTINAR / SCHMUDGEN)

def extractNonnegConstraints : TacticM (Array String) := do
  let goal ← getMainGoal
  goal.withContext do
    let mut constraints := #[]
    let mut idx := 0
    for localDecl in ← getLCtx do
      if localDecl.isImplementationDetail || localDecl.isAuxDecl then
        continue
      let typeText ← ppString localDecl.type
      let name := localDecl.userName
      if typeText.startsWith "0 ≤" then
        constraints := constraints.push (typeText.drop "0 ≤".length).trimAscii.toString
      else if typeText.endsWith "≥ 0" then
        let expr := (typeText.dropEnd "≥ 0".length).trimAscii.toString
        constraints := constraints.push expr
        evalTacticString s!"have _h_norm_{idx} : (0 : ℝ) ≤ {expr} := by linarith [{name}]"
        idx := idx + 1
      else
        match typeText.splitOn " ≤ " with
        | [lhs, rhs] =>
            let expr := s!"{rhs.trimAscii} - ({lhs.trimAscii})"
            constraints := constraints.push expr
            evalTacticString s!"have _h_norm_{idx} : (0 : ℝ) ≤ {expr} := by linarith [{name}]"
            idx := idx + 1
        | _ =>
          match typeText.splitOn " ≥ " with
          | [lhs, rhs] =>
              let expr := s!"{lhs.trimAscii} - ({rhs.trimAscii})"
              constraints := constraints.push expr
              evalTacticString s!"have _h_norm_{idx} : (0 : ℝ) ≤ {expr} := by linarith [{name}]"
              idx := idx + 1
          | _ => pure ()
    return constraints

def pstvWeightedTermString (constraintExprs : Array String)
    (factorIndices : List Nat) (term : SerializedWeightedSOSTerm) : String :=
  let weight := s!"(({backendToLean term.weight}) : ℝ)"
  let poly := s!"(({backendToLean term.poly.expr}) : ℝ)"
  let constraintParts := factorIndices.map fun i => s!"({constraintExprs[i]!})"
  let allParts := [weight] ++ constraintParts ++ [s!"{poly} ^ 2"]
  " * ".intercalate allParts

def pstvBlockTerms (constraintExprs : Array String)
    (block : SerializedCertBlock) : List String :=
  block.weighted_sos.map (pstvWeightedTermString constraintExprs block.multiplier_factor_indices)

def pstvCertRhs (constraintExprs : Array String)
    (blocks : List SerializedCertBlock) : String :=
  let allTerms := blocks.flatMap (pstvBlockTerms constraintExprs)
  match allTerms with
  | [] => "(0 : ℝ)"
  | xs => " + ".intercalate xs

def runPstvDecomp (command : String) (degreeBound : Nat)
    (blockBases : Option String := none)
    (certFile : Option String := none) : TacticM Unit := do
  let goalTarget ← normalizeNonnegGoal
  let constraints ← extractNonnegConstraints
  if constraints.isEmpty then
    throwError "{command} requires at least one constraint hypothesis of the form '0 ≤ g'"
  let result ← match certFile with
    | some path => (loadPstvResult path : MetaM PstvResult)
    | none =>
      let constraintStrs := ", ".intercalate constraints.toList
      (runPstvBackend command goalTarget constraintStrs degreeBound blockBases : MetaM PstvResult)
  if !result.success then
    match result.suggestion with
    | some s => throwError "{command} backend failed to find a certificate.\n\nHint: {s}"
    | none => throwError "{command} backend failed to find a certificate"
  let blocks := result.exact_certificate_blocks.getD []
  let rhs := pstvCertRhs constraints blocks
  evalTacticString s!"have _h_pstv_cert : (({goalTarget}) : ℝ) = {rhs} := by ring_nf"
  evalTacticString "rw [_h_pstv_cert]"
  evalTacticString "positivity"

def runPstvEmpty (command : String) (degreeBound : Nat)
    (blockBases : Option String := none)
    (certFile : Option String := none) : TacticM Unit := do
  let constraints ← extractNonnegConstraints
  if constraints.isEmpty then
    throwError "{command} requires at least one constraint hypothesis of the form '0 ≤ g'"
  let result ← match certFile with
    | some path => (loadPstvResult path : MetaM PstvResult)
    | none =>
      let constraintStrs := ", ".intercalate constraints.toList
      (runPstvBackend command "-1" constraintStrs degreeBound blockBases : MetaM PstvResult)
  if !result.success then
    match result.suggestion with
    | some s => throwError "{command} backend failed to find an emptiness certificate.\n\nHint: {s}"
    | none => throwError "{command} backend failed to find an emptiness certificate"
  let blocks := result.exact_certificate_blocks.getD []
  let rhs := pstvCertRhs constraints blocks
  evalTacticString s!"have _h_pstv_cert : (-1 : ℝ) = {rhs} := by ring_nf"
  evalTacticString s!"have _h_pstv_nonneg : (0 : ℝ) ≤ {rhs} := by positivity"
  evalTacticString "linarith"

syntax (name := putinarDecompTac) "putinar_decomp" "(" "degree" ":=" num ")" ("(" "block_bases" ":=" str ")")? : tactic
syntax (name := schmudgenDecompTac) "schmudgen_decomp" "(" "degree" ":=" num ")" ("(" "block_bases" ":=" str ")")? : tactic
syntax (name := putinarEmptyTac) "putinar_empty" "(" "degree" ":=" num ")" ("(" "block_bases" ":=" str ")")? : tactic
syntax (name := schmudgenEmptyTac) "schmudgen_empty" "(" "degree" ":=" num ")" ("(" "block_bases" ":=" str ")")? : tactic
syntax (name := putinarDecompCertTac) "putinar_decomp" "(" "cert" ":=" str ")" : tactic
syntax (name := schmudgenDecompCertTac) "schmudgen_decomp" "(" "cert" ":=" str ")" : tactic
syntax (name := putinarEmptyCertTac) "putinar_empty" "(" "cert" ":=" str ")" : tactic
syntax (name := schmudgenEmptyCertTac) "schmudgen_empty" "(" "cert" ":=" str ")" : tactic

elab_rules : tactic
  | `(tactic| putinar_decomp (degree := $d:num) $[( block_bases := $bb:str )]?) =>
    Lean.Elab.Tactic.focus do runPstvDecomp "putinar" d.getNat (bb.map (·.getString))
  | `(tactic| schmudgen_decomp (degree := $d:num) $[( block_bases := $bb:str )]?) =>
    Lean.Elab.Tactic.focus do runPstvDecomp "schmudgen" d.getNat (bb.map (·.getString))
  | `(tactic| putinar_empty (degree := $d:num) $[( block_bases := $bb:str )]?) =>
    Lean.Elab.Tactic.focus do runPstvEmpty "putinar" d.getNat (bb.map (·.getString))
  | `(tactic| schmudgen_empty (degree := $d:num) $[( block_bases := $bb:str )]?) =>
    Lean.Elab.Tactic.focus do runPstvEmpty "schmudgen" d.getNat (bb.map (·.getString))
  | `(tactic| putinar_decomp (cert := $c:str)) =>
    Lean.Elab.Tactic.focus do runPstvDecomp "putinar" 0 (certFile := some c.getString)
  | `(tactic| schmudgen_decomp (cert := $c:str)) =>
    Lean.Elab.Tactic.focus do runPstvDecomp "schmudgen" 0 (certFile := some c.getString)
  | `(tactic| putinar_empty (cert := $c:str)) =>
    Lean.Elab.Tactic.focus do runPstvEmpty "putinar" 0 (certFile := some c.getString)
  | `(tactic| schmudgen_empty (cert := $c:str)) =>
    Lean.Elab.Tactic.focus do runPstvEmpty "schmudgen" 0 (certFile := some c.getString)

end Sostactic
