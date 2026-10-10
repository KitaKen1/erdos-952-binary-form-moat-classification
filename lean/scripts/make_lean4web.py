#!/usr/bin/env python3
"""Flatten the three FC-matching proof entries and their dependency closure."""
import argparse
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[2]
source_root = root/'lean'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output-dir',type=Path,default=root/'lean4web')
parser.add_argument('--report',type=Path,default=source_root/'evidence/browser-generation.json')
parser.add_argument('--limit',type=int,help='Internal prefix diagnostic; not a complete publication')
args = parser.parse_args()
import_line = re.compile(r'^(?:(?:public|meta) )?import (?:(all) )?([\w.]+)\s*$',re.M)
seen = set()
ordered = []
external = {}
dependencies = {}
entry_targets = {
    'OpenAIVariant': 'Erdos952.erdos_952_openai',
    'GeneralizedVariant': 'Erdos952.erdos_952_openai_generalized_variant',
    'BinaryFormMoatClassification':
        'BinaryFormMoatClassification.binary_form_moat_classification',
}
entry_sources = {}
fc_checks = {}

def normalized(text):
    # FC's solved-answer notation elaborates to False in these two targets.
    return re.sub(r'\s+', '', text.replace('answer(False)', 'False'))

def target_statement(text, name):
    match = re.search(r'^theorem ' + re.escape(name) + r'\s*(:.*?)\s*:= by', text, re.M | re.S)
    assert match, 'Missing target theorem: ' + name
    return normalized(match[1])

for module, target in entry_targets.items():
    entry_path = source_root / (module + '.lean')
    fc_path = root / 'FClikelean' / (module + '.lean')
    entry_text = entry_path.read_text()
    fc_text = fc_path.read_text()
    name = target.rsplit('.', 1)[1]
    namespace = target.rsplit('.', 1)[0]
    assert 'namespace ' + namespace in entry_text and 'namespace ' + namespace in fc_text
    statement = target_statement(fc_text, name)
    assert target_statement(entry_text, name) == statement, module + ': FC statement mismatch'
    definitions = {}
    for definition in ['FewPrimeFactors']:
        pattern = r'^def ' + definition + r'\b[^\n]*\n(?:[^\n]+\n)*'
        fc_definition = re.search(pattern, fc_text, re.M)
        proof_definition = re.search(pattern, entry_text, re.M)
        assert bool(fc_definition) == bool(proof_definition), module + ': missing FC definition'
        if fc_definition:
            assert normalized(fc_definition[0]) == normalized(proof_definition[0]), module + ': FC definition mismatch'
            definitions[definition] = hashlib.sha256(normalized(fc_definition[0]).encode()).hexdigest()
    assert entry_text.rstrip().endswith('#print axioms ' + target), module + ': missing final axiom audit'
    assert not re.search(r'\b(?:sorry|admit|axiom)\b', entry_text), module + ': incomplete proof'
    entry_sources[module] = (entry_path, entry_text)
    fc_checks[module] = dict(
        fc_path=str(fc_path.relative_to(root)), fc_source_sha256=hashlib.sha256(fc_text.encode()).hexdigest(),
        target=target, statement_sha256=hashlib.sha256(statement.encode()).hexdigest(),
        definition_sha256=definitions, definitions_and_target_statement_match=True,
        answer_false_elaborated_as_false='answer(False)' in fc_text,
        final_target_axiom_print=True)

def close_file_scopes(text):
    """Close scopes normally ended by EOF in each original source file."""
    # Mask nested comments and strings before inspecting command boundaries.
    chars = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(chars):
        if depth:
            if text.startswith('/-',i): depth += 1; chars[i:i+2] = '  '; i += 2; continue
            if text.startswith('-/',i): depth -= 1; chars[i:i+2] = '  '; i += 2; continue
            if chars[i] != '\n': chars[i] = ' '
            i += 1; continue
        if string:
            if text[i] == '\\':
                chars[i] = ' '
                if i+1 < len(chars) and chars[i+1] != '\n': chars[i+1] = ' '
                i += 2; continue
            if text[i] == '"': string = False
            if chars[i] != '\n': chars[i] = ' '
            i += 1; continue
        if text.startswith('/-',i): depth = 1; chars[i:i+2] = '  '; i += 2; continue
        if text.startswith('--',i):
            while i < len(chars) and chars[i] != '\n': chars[i] = ' '; i += 1
            continue
        if text[i] == '"': string = True; chars[i] = ' '
        i += 1
    scopes = []
    for line in ''.join(chars).splitlines():
        line = line.strip()
        start = re.fullmatch(r'(?:@\[[^\n]*\]\s*)?(?:(?:noncomputable|public|private)\s+)*(section|namespace)(?:\s+([^\s]+))?',line)
        if start:
            scopes.extend((start[2] or '').split('.'))
            continue
        end = re.fullmatch(r'end(?:\s+([^\s]+))?',line)
        if end:
            assert scopes, 'Unexpected end: '+line
            names = end[1].split('.') if end[1] else ['']
            assert scopes[-len(names):] == names, (line,scopes[-len(names):])
            del scopes[-len(names):]
    return '\n'.join('end'+(' '+name if name else '') for name in reversed(scopes))

def locate(module):
    relative = Path(module.replace('.','/')+'.lean')
    local = source_root/relative
    if local.exists(): return local
    return source_root/'verification/lean435/vendor'/module.split('.')[0]/relative

def visit(module):
    if module in seen: return
    seen.add(module)
    path = locate(module)
    if not path.exists():
        assert module.startswith('Mathlib.'),module
        external.setdefault(module,False)
        return
    text = path.read_text()
    dependencies[module] = [m for full,m in import_line.findall(text)]
    for full,dependency in import_line.findall(text):
        visit(dependency)
        if dependency in external and full: external[dependency] = True
    ordered.append((module,path,text))

visit('Moat.Conjectures')
for module in entry_targets:
    visit(module)
support = [(m, p, t) for m, p, t in ordered if m not in entry_targets]
selected = support if args.limit is None else support[:args.limit]
pair_module = 'PFR.ForMathlib.Pair'
pair_dependents = {}
def uses_pair(module):
    if module not in pair_dependents:
        pair_dependents[module] = module == pair_module or any(uses_pair(m) for m in dependencies.get(module,[]))
    return pair_dependents[module]
header = 'module\n\n' + '\n'.join('public import '+m for m in sorted(external))
header += '\n' + '\n'.join('import all '+m for m in sorted(external) if external[m])
header += '''\n\n/-! Complete proofs of the three targets stated in FClikelean.
The final targets use the FC definitions and finite injective-sequence statements.
The custom proof dependencies are embedded below; only pinned Mathlib is imported.
Generated from the modular proof by lean/scripts/make_lean4web.py.
-/
@[expose] public section
set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option linter.redundantVisibility false
set_option linter.ambiguousOpen false
set_option warn.redundantExpose false
#guard Lean.versionString == "4.35.0-rc4"

-- Latest Mathlib makes spanSingleton a monoid-with-zero homomorphism.
-- The pinned snapshot has the same operation as an ordinary function.
namespace BinaryFormMoatLean4WebCompat
variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]
  (S : Submonoid R) [IsLocalization S P]

theorem spanSingleton_mul (x y : P) :
    FractionalIdeal.spanSingleton S x * FractionalIdeal.spanSingleton S y =
      FractionalIdeal.spanSingleton S (x * y) := by
  first
  | exact (map_mul (FractionalIdeal.spanSingleton S) x y).symm
  | apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton,
      Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem spanSingleton_one : FractionalIdeal.spanSingleton S (1 : P) = 1 := by
  first
  | exact map_one (FractionalIdeal.spanSingleton S)
  | apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_spanSingleton, FractionalIdeal.coe_one,
      Submodule.one_eq_span]

end BinaryFormMoatLean4WebCompat
\n'''
bodies = []
module_data = {}
removed_axiom_prints = 0
for i,(module,path,text) in enumerate(selected):
    body = import_line.sub('',text)
    body = re.sub(r'^module\s*$', '',body,flags=re.M)
    # Keep the proof terms, but avoid thousands of repeated LSP diagnostics.
    # The modular sources retain their complete intermediate axiom audits.
    body, removed = re.subn(r'^[ \t]*#print axioms[^\n]*(?:\n|$)', '', body, flags=re.M)
    removed_axiom_prints += removed
    # Original per-module visibility/exposure commands remain scoped to this
    # section. Module docstrings become ordinary provenance comments.
    body = body.replace('/-!','/-')
    # PFR's function-pair notation shares brackets with Lean constructor
    # patterns. Restore the original per-module import visibility instead of
    # leaking that notation into unrelated LeanPool/TauCeti source sections.
    if module == pair_module:
        assert '@[inherit_doc prod] notation3:100' in body
        body = body.replace('@[inherit_doc prod] notation3:100','@[inherit_doc prod] local notation3:100',1)
    # An exposed public definition cannot reference a private declaration in rc4.
    # All private helper names in this closure are distinct; export their proofs.
    body = re.sub(r'\bprivate (?=(?:noncomputable )?(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\b)', '', body)
    # Flattening introduces TauCeti.NumberField before some scoped opens which
    # originally saw only Mathlib's root NumberField namespace.
    body = re.sub(r'^(open [^\n]*)$',
                  lambda m: re.sub(r'(?<![\w.])(NumberField|Real)(?![\w.])', lambda n: '_root_.'+n[1], m[0]),
                  body, flags=re.M)
    if module == 'LeanPool.BooleanIsoperimetry.Harper':
        anchor = "      fun s hs₁ hs₂ => not_le.mp fun hs₃ => hs₁.not_ge <| Finset.le_max' _ _ <| by aesop⟩\n  grind +suggestions"
        assert body.count(anchor) == 1
        body = body.replace(anchor, anchor.rsplit('\n',1)[0]+'''\n  refine ⟨r, hr.1, hr.2.1, ?_⟩
  by_cases h : r < N
  · exact hr.2.2 (r + 1) (by omega) (by omega)
  · have hrN : r = N := by omega
    subst r
    simpa only [binomPrefix_full] using hb''')
    if module == 'TauCeti.NumberTheory.ArithmeticDirichletSeries.Basic':
        anchor = '''  simpa [zeroExtend_eq_extend] using
    (Function.extend_zero (Subtype.val : (Ideal (𝓞 K))⁰ → Ideal (𝓞 K)))'''
        assert body.count(anchor) == 1
        body = body.replace(anchor, '  simp [zeroExtend_eq_extend]')
    if module == 'TauCeti.NumberTheory.NumberField.Global.RayClass.Basic':
        for lemma in ['coe_idealsAwayInclusion', 'coe_integralIdealsAwayHom']:
            anchor = '  exact Subtype.ext (Units.ext (by simp [NumberFieldArithmetic.' + lemma + ']))'
            assert body.count(anchor) == (2 if lemma == 'coe_idealsAwayInclusion' else 1)
            # rc4's congr now discharges these definitional subtype equalities.
            body = body.replace(anchor, '')
    if module == 'TauCeti.NumberTheory.Chebotarev.TaggedFixedField':
        anchor = 'Subgroup.map_inf _ _ _ e.injective'
        assert body.count(anchor) == 1
        body = body.replace(anchor, 'Subgroup.map_inf _ _ e.toMonoidHom e.injective')
        anchor = 'Subgroup.map_comap_eq_self_of_surjective e.surjective'
        assert body.count(anchor) == 1
        body = body.replace(anchor, 'Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective')
    if module in ['TauCeti.NumberTheory.NumberField.Global.RayClass.Integral',
                  'TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Basic']:
        old_mul = 'FractionalIdeal.spanSingleton_mul_spanSingleton'
        old_one = 'FractionalIdeal.spanSingleton_one'
        integral = module.endswith('RayClass.Integral')
        assert body.count(old_mul) == (2 if integral else 1)
        assert body.count(old_one) == (1 if integral else 0)
        body = body.replace(old_mul, 'BinaryFormMoatLean4WebCompat.spanSingleton_mul')
        body = body.replace(old_one, 'BinaryFormMoatLean4WebCompat.spanSingleton_one')
    pair_notation = ('local notation3:100 "⟨" X ", " Y "⟩" => _root_.prod X Y\n'
                     if module != pair_module and uses_pair(module) else '')
    assert not re.search(r'^(?:(?:public|meta) )?import\b|^module\b',body,re.M),module
    closing = close_file_scopes(body)
    block = '\n-- Source: '+module+'\nsection Source'+str(i)+'\n'+pair_notation+body.strip()+'\n'+closing+'\nend Source'+str(i)+'\n'
    bodies.append(block)
    module_data[module] = dict(path=str(path.relative_to(source_root)),sha256=hashlib.sha256(text.encode()).hexdigest())
result = header + '\n'.join(bodies)
core_targets = ['BinaryFormMoat.irreducible_homogenization_uniformMoat',
           'BinaryFormMoat.uniformMoat_of_not_isLinearPower','BinaryFormMoat.classification']
fc_targets = list(entry_targets.values())
if args.limit is None:
    result += '''\n-- The original all-degree target, with all original hypotheses.
example (F : BinaryFormMoat.Form) (d : ℕ) (hF : F ≠ 0)
    (hd : 0 < d) (hhom : F.IsHomogeneous d) :
    BinaryFormMoat.UniformMoat F ↔ ¬ BinaryFormMoat.IsLinearPower F :=
  BinaryFormMoat.classification F d hF hd hhom
\n'''
    for module, (entry_path, entry_text) in entry_sources.items():
        entry_body = import_line.sub('', entry_text).replace('/-!', '/-')
        entry_body = re.sub(r'\bprivate (?=(?:noncomputable )?(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\b)',
                            '', entry_body)
        result += '\n-- Source: ' + module + ' (FC target and complete proof)\n' + entry_body.strip() + '\n'
    assert re.findall(r'^#print axioms (.+)$', result, flags=re.M) == fc_targets
args.output_dir.mkdir(parents=True,exist_ok=True)
output = args.output_dir/'BinaryFormMoatLean4Web.lean'
output.write_text(result)
args.report.parent.mkdir(parents=True,exist_ok=True)
args.report.write_text(json.dumps({'BinaryFormMoatLean4Web':dict(
    source_modules=[m for m,p,t in selected],source_module_files=module_data,
    fc_target_entry_points={module:dict(path=str(path.relative_to(source_root)),
        sha256=hashlib.sha256(text.encode()).hexdigest(),target=entry_targets[module])
        for module,(path,text) in entry_sources.items()},
    fc_statement_checks=fc_checks,
    fc_targets=fc_targets if args.limit is None else [],
    generated_sha256=hashlib.sha256(result.encode()).hexdigest(),lines=len(result.splitlines()),
    targets=fc_targets if args.limit is None else [],core_targets=core_targets,
    embedded_axiom_print_commands_removed=removed_axiom_prints,
    diagnostics_policy='Only the three final FC target axiom audits are printed.',
    full_all_degree_classification_in_this_file=args.limit is None,
    imports_only_mathlib=True,mathlib_imports=external,
    transforms=['topological dependency flattening','imports collected into the header',
                'module commands removed','module settings scoped by source section',
                'module docstrings converted to ordinary comments',
                'intermediate axiom print diagnostics omitted; final FC target audits retained',
                'PFR function-pair notation scoped to its original dependency closure',
                'private proof helpers exposed for rc4 public definitions',
                'root NumberField and Real namespace opens qualified',
                'Harper layer locator uses explicit maximality proof',
                'zeroExtend_zero simplified for current simp set',
                'RayClass definitional congruence drops already-discharged subgoals',
                'TaggedFixedField map homomorphisms made explicit',
                'spanSingleton multiplicativity and unit proofs support pinned and latest Mathlib without deprecated aliases'],
    mathematical_definitions_and_main_hypotheses_retained=True)},indent=2)+'\n')
print('Generated',output,'from',len(selected),'support modules and',len(entry_sources),
      'FC-matching proof entries;',len(result.splitlines()),'lines')
