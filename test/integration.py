"""CLI boundary checks against real compiler inputs and the official validator.

Use existing general formal contracts; no Agda sample-state modules are created.
"""
import hashlib
import itertools
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from open_parameters import verify_open_parameters
from dependent_evidence import verify_dependent_evidence
from recursive_core import verify_recursive_core
from structured_indices import verify_structured_indices
from callbacks import verify_callbacks
from dependent_record_path import verify_dependent_record_path
from natural_values import verify_natural_values
from tagged_sums import verify_tagged_sums
from report_accounting import verify_report_accounting
from native_callbacks import verify_native_callbacks
from callable_fields import verify_callable_fields
from equality_statements import verify_equality_statements
from symbolic_levels import verify_symbolic_levels
from dependent_callbacks import verify_dependent_callbacks
from multi_callbacks import verify_multi_callbacks
from schema_records import verify_schema_records
from dependent_schemas import verify_dependent_schemas
from arithmetic_indices import verify_arithmetic_indices
from dependent_patterns import verify_dependent_patterns
from contextual_indices import verify_contextual_indices
from dependent_family_parameters import verify_dependent_family_parameters
from specialized_callbacks import verify_specialized_callbacks
from index_closures import verify_index_closures


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def check_source_catalog(inventory):
    for module in inventory["modules"]:
        catalog = module["sourceCorrespondence"]
        text = module["sourceText"].encode("utf-8")
        check(catalog["version"] == 1 and catalog["coordinateSystem"] == "utf8-byte-offsets-zero-based-half-open",
              "unknown source catalog schema")
        check(catalog["checkedTextDigest"] == hashlib.sha256(text).hexdigest(), "stale catalog text")
        entries = catalog["occurrences"]
        by_id = {e["id"]: e for e in entries}
        check(len(by_id) == len(entries), "source occurrences collapsed")
        definitions = {d["name"] for d in module["definitions"]}
        check({a["symbol"] for a in catalog["declarationAnchors"]} == definitions,
              "declaration anchor accounting is incomplete")
        for entry in entries:
            check(entry["module"] == module["name"], "source occurrence changed module")
            check(entry["parent"] is None or entry["parent"] in by_id, "dangling source parent")
            check(entry["anchor"] is None or entry["anchor"] in by_id, "dangling binding anchor")
            check(entry["owner"] is None or entry["owner"] in definitions, "unknown source owner")
            check((entry["owner"] is None) == (entry["ownerUnavailable"] is not None), "ownership status contradicts evidence")
            if entry["owner"] is not None:
                check(entry["ownerCandidates"] == [entry["owner"]], "ambiguous source owner guessed")
            if entry["anchor"] is not None:
                check(entry["owner"] == by_id[entry["anchor"]]["owner"], "child lost lexical owner")
            check(entry["rangeUnavailable"] != "invalid-source-range", "compiler coordinate conversion failed")
            previous = 0
            for interval in entry["intervals"]:
                start, end = interval["start"], interval["end"]
                check(previous <= start < end <= len(text), "invalid source interval")
                text[start:end].decode("utf-8")
                previous = end
            check(bool(entry["intervals"]) == (entry["rangeUnavailable"] is None), "source range status is inconsistent")
        for anchor in catalog["declarationAnchors"]:
            check(bool(anchor["occurrences"]) == (anchor["unavailable"] is None), "declaration anchor status is inconsistent")
            check(all(by_id[i]["owner"] == anchor["symbol"] for i in anchor["occurrences"]), "declaration anchor lost owner")


def signature_shape(ty):
    # Compare references as input positions using each tree's actual binder
    # stack, independently of raw de Bruijn numbers or binder display names.
    def info(i):
        check((i["hiding"], i["relevance"], i["quantity"]) == ("explicit", "relevant", "unrestricted"), "unsupported transported modality")
    def term(t, stack):
        if t["tag"] == "variable":
            check(0 <= t["index"] < len(stack), "unresolved signature reference")
            es = t["eliminations"]
            check(not es or (len(es) == 1 and es[0]["tag"] == "project" and isinstance(es[0]["symbol"], str)
                             and es[0]["symbol"]), "unsupported signature receiver elimination")
            return ("input", stack[t["index"]], tuple(e["symbol"] for e in es))
        check(t["tag"] in ("definition", "constructor"), "unsupported signature term")
        args = []
        for a in t["eliminations"]:
            check(a["tag"] == "apply", "unsupported signature elimination")
            info(a["argument"]["info"])
            args.append(term(a["argument"]["value"], stack))
        return (t["tag"], t["symbol"], tuple(args))
    domains, stack = [], []
    while ty["term"]["tag"] == "pi":
        t = ty["term"]
        info(t["domain"]["info"])
        check(t["domain"]["type"]["term"]["tag"] == "definition", "higher-order signature domain")
        domains.append(term(t["domain"]["type"]["term"], stack))
        check(isinstance(t["codomain"]["binds"], bool), "missing signature binder mode")
        if t["codomain"]["binds"]:
            stack.insert(0, len(domains) - 1)
        ty = t["codomain"]["body"]
    check(ty["term"]["tag"] == "definition", "unsupported signature result")
    return (tuple(domains), term(ty["term"], stack))


def check_target_trace(output):
    model = (output / "model.sysml").read_bytes()
    report = json.loads((output / "correspondence.json").read_text())
    trace = report["sourceCorrespondence"]
    check(trace["version"] == 1 and trace["coordinateSystem"] == "utf8-byte-offsets-zero-based-half-open", "unknown target trace schema")
    check(trace["artifactDigest"] == hashlib.sha256(model).hexdigest(), "stale target trace")
    check(trace["sourceAlignment"] in ("partial", "unavailable"), "bounded alignment claimed full source coverage")
    targets = {t["id"]: t for t in trace["targetOccurrences"]}
    checked = {c["id"]: c for c in trace["checkedOccurrences"]}
    derivations = {d["id"]: d for d in trace["derivations"]}
    roots = {(r["owner"], r["root"]): r for r in trace["checkedRoots"]}
    inventory = json.loads((output / "inventory.json").read_text())
    definitions = {d["name"]: d for m in inventory["modules"] for d in m["definitions"]}
    source_catalog = {o["id"]: o for m in inventory["modules"] for o in m["sourceCorrespondence"]["occurrences"]}
    sources = {o["id"]: o for o in trace["sourceOccurrences"]}
    check(all(source_catalog.get(key) == value for key, value in sources.items()), "trace source differs from checked-text catalog")
    def expand(value):
        if isinstance(value, dict):
            if set(value) == {"$node"}:
                node = inventory["nodes"][value["$node"]]
                return expand(node["object"] if "object" in node else node["array"])
            return {k: expand(v) for k, v in value.items()}
        if isinstance(value, list):
            return [expand(v) for v in value]
        return value
    for module in inventory["modules"]:
        alignment = module["sourceAlignment"]
        check(alignment["version"] == 1 and alignment["ruleVersion"] == 1, "unknown alignment rule")
        for definition in alignment["definitions"] + alignment["signatures"]:
            check(not definition["links"] or definition["unavailable"] is None, "unavailable alignment retained exact links")
            for link in definition["links"]:
                locator = link["checked"]
                value = expand(definitions[locator["owner"]][locator["root"]])
                for step in locator["path"]:
                    value = value[step]
                check(isinstance(value, dict), "aligned path is not a checked term")
                check(source_catalog[link["source"]]["owner"] == locator["owner"] == definition["owner"], "alignment owner mismatch")
                if link["rule"] == "source.explicit-signature":
                    check(locator["root"] == "type" and source_catalog[link["signature"]]["role"] in ("function-signature", "constructor-signature")
                          and source_catalog[link["signature"]]["owner"] == locator["owner"]
                          and source_catalog[link["source"]]["anchor"] == link["signature"], "missing source signature evidence")
                else:
                    check(source_catalog[link["clause"]]["role"] == "clause", "missing source clause evidence")
                check(link["rule"] in ("source.direct-first-order", "source.compiled-clause", "source.explicit-signature") and link["ruleVersion"] == 1, "unversioned source rule")
                if link["rule"] == "source.compiled-clause":
                    check(link["source"] == link["clause"] and locator["root"] == "compiled", "case derivation lost its clause")
                    replay = link["replay"]
                    node, path, visited = expand(definitions[locator["owner"]]["compiled"]), [], [[]]
                    for split in replay["splits"]:
                        check(node["tag"] == "case" and split["path"] == path and split["argument"] == node["argument"]["value"], "case replay lost split position")
                        branch = node["constructors"][split["branch"]]
                        check(branch["symbol"] == split["constructor"] and branch["branch"]["arity"] == split["arity"], "case replay lost constructor identity")
                        path = path + ["constructors", split["branch"], "branch", "tree"]
                        check(split["child"] == path, "case replay jumped between branches")
                        visited.append(path)
                        node = branch["branch"]["tree"]
                    check(node["tag"] == "done" and replay["leaf"] == path and locator["path"] in visited, "case replay did not reach the verified leaf")
                    permutation = replay["binderPermutation"]
                    check(len(permutation) == len(set(permutation)) == len(node["binders"]), "case replay lost binder permutation")
                    check(any(l["rule"] == "source.direct-first-order" and l["clause"] == link["clause"] and l["checkedClause"] == link["checkedClause"]
                              and l["bindings"] == link["bindings"] and l["checked"]["root"] == "compiled" and l["checked"]["path"] == path + ["body"]
                              for l in definition["links"]), "case replay has no verified source RHS")
    templates = {(r["owner"], r["root"]): r["value"] for r in trace["templateRoots"]}
    for (owner, field), value in templates.items():
        check(owner in definitions and expand(definitions[owner].get(field)) == value, "template root is not the checked inventory field")
    for item in roots.values():
        template = item["template"]
        check((template["owner"], template["root"]) in templates, "missing specialization template")
        if item["preparation"] is None:
            check(item["value"] == templates[template["owner"], template["root"]], "unspecialized checked root changed")
        else:
            def has_open(value):
                if isinstance(value, dict):
                    return "openParameter" in value or "openFamily" in value or any(has_open(v) for v in value.values())
                return isinstance(value, list) and any(has_open(v) for v in value)
            expected = "native.open-parameter-schema" if has_open(item["preparation"]["arguments"]) else "native.static-specialization"
            check(item["preparation"]["rule"] == expected, "missing or misclassified preparation rule")
    check(len(targets) == len(trace["targetOccurrences"]), "target occurrences collapsed")
    check(len(checked) == len(trace["checkedOccurrences"]), "checked occurrences collapsed")
    values = {}
    for identifier, occurrence in checked.items():
        value = roots[occurrence["owner"], occurrence["root"]]["value"]
        for step in occurrence["path"]:
            value = value[step]
        check(occurrence["unavailable"] is None and occurrence["valueDigest"] is not None, "unresolved checked occurrence")
        values[identifier] = value
        check((occurrence["sourcePrecision"] in ("exact", "derived")) == bool(occurrence["sourceLinks"]), "source precision lacks alignment evidence")
        for link in occurrence["sourceLinks"]:
            check(link["source"] in sources, "source link does not resolve")
            check(link["checked"] == {k: occurrence[k] for k in ("owner", "root", "path")}, "source link changed checked occurrence")
            if link["rule"] in ("source.compiled-clause", "source.explicit-signature"):
                check(occurrence["sourcePrecision"] == "derived", "structural derivation claimed exact source identity")
            preparation = roots[occurrence["owner"], occurrence["root"]]["preparation"]
            if preparation is not None:
                check(preparation["arguments"] == [] and preparation["sourceTransport"] in ("same-term-structure", "same-signature-structure"),
                      "template alignment promoted through specialization")
                check(link["preparation"]["template"] == link["checked"] and link["preparation"]["rule"] == "source." + preparation["sourceTransport"],
                      "missing verified preparation evidence")
                root = roots[occurrence["owner"], occurrence["root"]]
                before, after = templates[occurrence["owner"], occurrence["root"]], root["value"]
                if preparation["sourceTransport"] == "same-term-structure":
                    def erase_modality(v):
                        if isinstance(v, dict): return {k: erase_modality(x) for k, x in v.items() if k != "modality"}
                        if isinstance(v, list): return [erase_modality(x) for x in v]
                        return v
                    check(occurrence["root"] == "compiled" and erase_modality(before) == erase_modality(after), "identity preparation changed term structure")
                else:
                    check(occurrence["root"] == "type" and signature_shape(before) == signature_shape(after), "signature preparation changed resolved telescope structure")
    rules = {(r["id"], r["version"]) for r in trace["rules"]}
    def evidence(item):
        check((item["rule"], item["ruleVersion"]) in rules, "unversioned derivation rule")
        check(all(i in checked for i in item["inputs"]), "broken derivation premise")
        for parent in item["steps"]:
            evidence(parent)
    by_path = {}
    for parent in targets.values():
        by_path.setdefault(tuple(parent["path"]), []).append(parent)
    for identifier, target in targets.items():
        check(target["derivation"] in derivations, "missing target derivation")
        spans = target["intervals"]
        check(len(spans) == 1, "unexpected target interval count")
        a, b = spans[0]["start"], spans[0]["end"]
        check(0 <= a < b <= len(model), "invalid target interval")
        model[a:b].decode("utf-8")
        derivation = derivations[target["derivation"]]
        check(derivation["outputs"] == [identifier], "wrong derivation output")
        check(all(i in checked for i in derivation["inputs"]), "broken checked-to-target reference")
        evidence(derivation["evidence"])
        if target["checkedPrecision"] == "derived":
            check(bool(derivation["inputs"]), "derived target has no checked evidence")
        if target["sourcePrecision"] == "derived":
            check(derivation["inputs"] and all(checked[i]["sourcePrecision"] in ("exact", "derived") for i in derivation["inputs"]),
                  "unresolved source input promoted through target derivation")
            def no_boundary(e):
                return e["unavailable"] is None and all(no_boundary(s) for s in e["steps"])
            check(no_boundary(derivation["evidence"]), "generated boundary promoted to source-derived")
        for depth in range(len(target["path"])):
            for parent in by_path.get(tuple(target["path"][:depth]), []):
                span = parent["intervals"][0]
                check(span["start"] <= a < b <= span["end"], "child span escapes marked parent")
        if target["role"] == "relation-endpoint":
            step = derivation["evidence"]
            for reference in step["inputs"]:
                value = values[reference]
                if value.get("tag") == "variable":
                    slot = step["premises"][value["index"]]
                    check(model[a:b].decode() == f"'witness{slot}'", "relation endpoint lost Abs/NoAbs witness substitution")
    return trace, values


generator, repository, validator, java = sys.argv[1:]
repository = Path(repository).resolve()
validator = Path(validator).resolve() / "share/agda2sysml-validator/sysml"

with tempfile.TemporaryDirectory(prefix="agda2sysml-integration-") as work:
    work = Path(work)
    for directory in ("spec", "contracts"):
        shutil.copytree(repository / directory, work / directory,
                        ignore=shutil.ignore_patterns("_build", "*.agdai"))
    mapping = work / "boolean.yaml"
    mapping.write_text("""mapping-version: 2
project:
  name: Formal Boolean operations
  agda-library: spec/agda2sysml-spec.agda-lib
  roots: [Agda2SysML.Foundation]
models:
  negation:
    module: Agda2SysML.Foundation
    state: {type: Bool}
    transition:
      encoding: function
      symbol: not
      arguments: {before: {position: 0}}
      result: {state: return}
  conjunction:
    module: Agda2SysML.Foundation
    state: {type: Bool}
    transition:
      encoding: function
      symbol: _∧_
      arguments: {before: {position: 0}}
      result: {state: return}
""", encoding="utf-8")

    def run_automatic(root, output, status, *options, library=None):
        result = subprocess.run([generator, "generate", "--library", str(library or (work / "spec/agda2sysml-spec.agda-lib")),
                                 "--root", root, "--output", str(output), *options],
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                env={**os.environ, "AGDA2SYSML_VERIFY_ENCODING": "1"})
        check(result.returncode == status, f"automatic generation: {result.returncode}\n{result.stdout}\n{result.stderr}")
        if (output / "manifest.json").exists():
            check_target_trace(output)
        return result

    self_output = work / "self"
    run_automatic("Agda2SysML", self_output, 2, "--diagnostic")
    self_inventory = json.loads((self_output / "inventory.json").read_text())
    check_source_catalog(self_inventory)
    self_report = json.loads((self_output / "correspondence.json").read_text())
    natural_evidence = verify_natural_values(self_output)
    check(natural_evidence == {'operations': 8, 'comparisons': 344, 'invalidCasesRejected': 6},
          "finite-natural adapters lack complete arithmetic results and inconsistent-evidence refusals")
    sum_evidence = verify_tagged_sums(self_output)
    accounting_evidence = verify_report_accounting(self_output)
    native_callback_evidence = verify_native_callbacks(self_output)
    callable_field_evidence = verify_callable_fields(self_output)
    statement_evidence = verify_equality_statements(self_output)
    level_evidence = verify_symbolic_levels(self_output)
    dependent_callback_evidence = verify_dependent_callbacks(self_output)
    multi_callback_evidence = verify_multi_callbacks(self_output)
    schema_record_evidence = verify_schema_records(self_output)
    dependent_schema_evidence = verify_dependent_schemas(self_output)
    arithmetic_index_evidence = verify_arithmetic_indices(self_output)
    pattern_evidence = verify_dependent_patterns(self_output)
    contextual_evidence = verify_contextual_indices(self_output)
    family_evidence = verify_dependent_family_parameters(self_output)
    specialized_evidence = verify_specialized_callbacks(self_output)
    closure_evidence = verify_index_closures(self_output)
    check(closure_evidence['operations'] == 3 and closure_evidence['statements'] == 4
          and closure_evidence['comparisons'] >= 117
          and closure_evidence['invalidCasesRejected'] >= 11
          and closure_evidence['bodyMutationsDetected'] == 3
          and closure_evidence['functionIdentityNotStored'],
          'dependent-index closures lack complete conversion, operation, law or refusal checks')
    check(specialized_evidence['operations'] == 3
          and specialized_evidence['comparisons'] >= 48
          and specialized_evidence['invalidCasesRejected'] >= 11
          and specialized_evidence['bodyMutationsDetected'] == 3
          and specialized_evidence['emptyConstraintMutationDetected'],
          'recursive substitution and closed instantiation lack complete results or refusal checks')
    check(family_evidence['operations'] == 7
          and family_evidence['comparisons'] >= 68
          and family_evidence['invalidCasesRejected'] >= 19
          and family_evidence['mutationsDetected'] == 7,
          'dependent and partial families lack complete operations or mismatch checks')
    check(contextual_evidence['operations'] == 8
          and contextual_evidence['comparisons'] >= 50
          and contextual_evidence['invalidCasesRejected'] >= 12
          and contextual_evidence['mutationsDetected'] == 9,
          'computed dependent membership lacks complete operations or mismatch checks')
    check(pattern_evidence['operations'] == 8
          and pattern_evidence['statements'] == 6
          and pattern_evidence['comparisons'] >= 1000
          and pattern_evidence['invalidCasesRejected'] >= 18
          and pattern_evidence['bodyMutationsDetected'] == 14
          and pattern_evidence['differentContextSizes'] > 0
          and pattern_evidence['completeEvidencePreserved'],
          'dependent pattern matches lack complete operations, evidence preservation, or refusal checks')
    check(arithmetic_index_evidence['operations'] == 7
          and arithmetic_index_evidence['statements'] == 8
          and arithmetic_index_evidence['comparisons'] >= 1000
          and arithmetic_index_evidence['invalidCasesRejected'] == 12
          and arithmetic_index_evidence['bodyMutationsDetected'] == 15
          and arithmetic_index_evidence['differentContextSizes'] > 0
          and arithmetic_index_evidence['completeEvidencePreserved'],
          'arithmetic indices lack complete values, preserved bounds, or rejection checks')
    check(dependent_schema_evidence['operations'] == 11
          and dependent_schema_evidence['comparisons'] >= 102
          and dependent_schema_evidence['invalidCasesRejected'] >= 160
          and dependent_schema_evidence['bodyMutationsDetected'] == 24
          and dependent_schema_evidence['structuredStates']
          and dependent_schema_evidence['completeEvidencePreserved'],
          'dependent schema construction and relation conversions lack complete behavior or refusal checks')
    check(schema_record_evidence['operations'] == 13
          and schema_record_evidence['statements'] == 10
          and schema_record_evidence['statementMutationsDetected'] == 20
          and schema_record_evidence['comparisons'] >= 342
          and schema_record_evidence['invalidBindingsRejected'] >= 62
          and schema_record_evidence['bodyMutationsDetected'] == 34
          and schema_record_evidence['proofCallbackChecks'] == 24,
          'stored schema conversions lack complete values, binding refusals, or mutation checks')
    check(multi_callback_evidence['operations'] == 7
          and multi_callback_evidence['comparisons'] >= 230
          and multi_callback_evidence['invalidBindingsRejected'] >= 11
          and multi_callback_evidence['bodyMutationsDetected'] == 7
          and multi_callback_evidence['dependentArguments']
          and multi_callback_evidence['completeResultsAndOriginsPreserved'],
          'multiargument callbacks lack complete behavior, dependent binding or mutation checks')
    check(dependent_callback_evidence == {'operations': 6, 'comparisons': 360,
          'evidenceCallbacksExercised': 12, 'invalidBindingsRejected': 15,
          'bodyMutationsDetected': 6},
          'indexed callbacks lack complete evaluator, evidence, refusal or mutation checks')
    check(level_evidence['operations'] == 10 and level_evidence['comparisons'] >= 700
          and level_evidence['invalidCasesRejected'] >= 30
          and level_evidence['nativeStatementsExercised'] == 4 and level_evidence['bodyMutationDetected'],
          'symbolic universe operations lack complete behavior and refusal checks')
    check(statement_evidence['expectedStatements'] == 33
          and statement_evidence['executedStatements'] == 33
          and statement_evidence['computedIndexMutationsDetected'] == 5
          and statement_evidence['conclusionMutationDetected']
          and statement_evidence['premiseMutationDetected']
          and statement_evidence['proofSourcesRetained'],
          'native theorem statements lack behavior, input evidence or provenance checks')
    check(callable_field_evidence['operations'] == 6
          and callable_field_evidence['comparisons'] >= 5000
          and callable_field_evidence['invalidCasesRejected'] >= 15
          and callable_field_evidence['capturedLambdaComparisons'] >= 1656
          and callable_field_evidence['nativeStatements'] == 4
          and callable_field_evidence['lambdaMutationsDetected'] == 2,
          'decision-tree normalization, captured guards, or rule-list behavior was not verified')
    check(native_callback_evidence['operations'] == 8 and native_callback_evidence['comparisons'] >= 400
          and native_callback_evidence['invalidCasesRejected'] >= 15,
          'native unary callbacks lack complete results and invalid-binding checks')
    check(accounting_evidence['operations'] == 4 and accounting_evidence['comparisons'] >= 200
          and accounting_evidence['invalidCasesRejected'] == 28 and accounting_evidence['unusedRuntimeInputs'] == 0,
          'existing report accounting lacks complete counts, identity preservation or invalid-input refusals')
    check(sum_evidence['operations'] == 7 and sum_evidence['tabulationComparisons'] == 30
          and sum_evidence['comparisons'] >= 100 and sum_evidence['invalidCasesRejected'] == 36
          and sum_evidence['constructionComparisons'] >= 100 and sum_evidence['lookupComparisons'] >= 100
          and sum_evidence['computedSchemaRefusals'] == 18
          and sum_evidence['repeatedConstructorSchemas'] > 0 and sum_evidence['completePayloadsAndEvidencePreserved'],
          "tagged-sum adapters lack complete results, distinct equal-schema constructors or validity refusals")
    open_evidence = verify_open_parameters(self_output)
    check(open_evidence["comparisons"] >= 700 and open_evidence["invalidBindingsRejected"] == 5,
          "open algorithms lack parsed-target behavior and parameter checks")
    dependent_evidence = verify_dependent_evidence(self_output)
    check(dependent_evidence["comparisons"] == 162 and dependent_evidence["invalidCasesRejected"] == 8,
          "dependent evidence lacks complete-result and invalid-index/family checks")
    recursive_evidence = verify_recursive_core(self_output)
    check(recursive_evidence["totalComparisons"] >= 1000 and recursive_evidence["invalidCasesRejected"] >= 10,
          "recursive core lacks parsed results and index/finiteness/capture checks")
    structured_evidence = verify_structured_indices(self_output)
    check(structured_evidence["comparisons"] == 18116 and structured_evidence["appendComparisons"] == 9160
          and structured_evidence["invalidSchemasRejected"] == 17
          and structured_evidence["repeatedPositions"] > 1000 and structured_evidence["reorderedBindings"] == 3,
          "structured indices lack ordered schemas, complete members, or invalid-index refusals")
    callback_evidence = verify_callbacks(self_output)
    check(callback_evidence == {'comparisons': 220, 'invalidCasesRejected': 6, 'operations': 5},
          "callback consumers lack complete outcomes and binding/schema refusals")
    record_path_evidence = verify_dependent_record_path(self_output)
    check(record_path_evidence == {'comparisons': 120, 'invalidCasesRejected': 12, 'operations': 4},
          "dependent-record path lacks complete members and projected index refusals")
    self_manifest = json.loads((self_output / "manifest.json").read_text())
    check(self_manifest["mappingDigest"] is None and self_manifest["mappingVersion"] is None
          and self_manifest["selectionProfile"] == "declarations", "default generation required a hidden mapping")
    own = {d["name"] for module in self_inventory["modules"]
           if module["source"]["library"] == self_inventory["library"] for d in module["definitions"]}
    catalogue = self_report["declarationCatalogue"]
    check({item["symbol"] for item in catalogue} == own, "default catalogue omitted project declarations")
    check(all(not item["contract"] or item["kind"] == "function" for item in catalogue),
          "a structure used by a proof was mislabeled as a proof contract")
    check(own <= {row["symbol"] for row in self_report["obligations"]}, "default requirement selection omitted declarations")
    modules = {module["name"]: module for module in self_inventory["modules"]}
    for item in catalogue:
        source = modules[item["module"]]["sourceText"].encode()
        previous = 0
        chunks = []
        for span in item["sourceIntervals"]:
            a, b = span["start"], span["end"]
            check(previous <= a < b <= len(source), "documentary declaration has overlapping/invalid source intervals")
            chunks.append(source[a:b].decode()); previous = b
        check(item["sourceExcerpt"] == "\n".join(chunks), "documentary source differs from checked text")
    check(not self_report["complete"] and any(row["status"] == "textual" for row in self_report["obligations"]),
          "documentary source concealed unsupported computation")
    check(any("Resolution.resolve#" in item["symbol"] and item["sourceExcerpt"] for item in catalogue),
          "the self model lost its principal resolution algorithm")
    check(any(item["contract"] and "BooleanLowering.lower-preserves#" in item["symbol"] for item in catalogue),
          "the self model lost its preservation contract")
    check(any(row["target"] and "NaturalValues.sourceAdd#" in row["symbol"] for row in self_report["obligations"]),
          "default generation emitted no independently selected arithmetic body")
    review = (self_output / "review.html").read_text()
    payload = review.split('<script type="application/json" id="payload">',1)[1].split('</script>',1)[0]
    review_data = json.loads(payload)
    check(len(review_data["declarations"]) == len(own) and not review_data["complete"], "viewer misreported self coverage")
    check("<" not in payload and "@@PAYLOAD@@" not in review, "viewer source can break its JSON data boundary")
    subprocess.run(["node", str(repository / "test/review.cjs"), str(self_output / "review.html")], check=True)
    for filename, digest in self_manifest["artifacts"].items():
        check(hashlib.sha256((self_output / filename).read_bytes()).hexdigest() == digest, "default artifact digest mismatch")

    # Local roles are additive: a narrow state-machine annotation cannot hide
    # independent defaults. A conflicting source library must fail before output.
    annotated = work / "automatic-annotated"
    run_automatic("Agda2SysML.Foundation", annotated, 2, "--diagnostic", "--mapping", str(mapping))
    annotated_report = json.loads((annotated / "correspondence.json").read_text())
    check(any("Foundation._++_#" in row["symbol"] and row["kind"] == "behavior"
              for row in annotated_report["obligations"]), "mapping narrowed the default declaration scope")
    mismatch = run_automatic("Agda2SysML", work / "root-conflict", 1, "--mapping", str(mapping))
    check("requested roots" in mismatch.stderr and not (work / "root-conflict").exists(), "conflicting annotation roots were ignored")

    default_workflow = work / "default-workflow"
    run_automatic("RegisterWorkflow", default_workflow, 0, library=work / "contracts/contracts.agda-lib")
    default_manifest = json.loads((default_workflow / "manifest.json").read_text())
    check(default_manifest["complete"] and default_manifest["mappingDigest"] is None,
          "a complete independent workflow still required YAML")
    default_report = json.loads((default_workflow / "correspondence.json").read_text())
    check(any(row["target"] and "RegisterWorkflow.sequence#" in row["symbol"] for row in default_report["obligations"]),
          "default workflow omitted its composed transition body")
    subprocess.run(["node", str(repository / "test/review.cjs"), str(default_workflow / "review.html")], check=True)

    def run(mode, config, output, status, *options):
        result = subprocess.run([generator, mode, "--mapping", str(config),
                                 "--output", str(output), *options],
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                env={**os.environ, "AGDA2SYSML_VERIFY_ENCODING": "1"})
        check(result.returncode == status,
              f"{mode}: expected {status}, got {result.returncode}\n{result.stdout}\n{result.stderr}")
        if mode == "generate" and (output / "correspondence.json").exists():
            check_target_trace(output)

    natural_output = work / "naturals"
    run("generate", work / "contracts/naturals.yaml", natural_output, 0)
    natural_model = (natural_output / "model.sysml").read_text()
    check(" < *)" in natural_model, "native natural carrier admitted infinity")
    natural_cases = []
    # Pilot's integer parser/evaluator is bounded; arbitrary precision is
    # checked independently in the target-expression algebra suite.
    for left, right in ((0, 0), (0, 7), (11, 3), (3, 11), (10**4, 10**4 + 1)):
        for function, result in (("sourceAdd", left + right),
                                 ("sourceMultiply", left * right),
                                 ("sourceSubtract", max(0, left - right))):
            natural_cases += [f"'Agda2SysML.NaturalValues.{function}'({left}, {right}) == {result}", "true"]
    subprocess.run([java, "--class-path", str(validator / "jupyter-sysml-kernel-0.58.0-all.jar"),
                    str(repository / "test/TargetEvaluation.java"), str(validator / "sysml.library"),
                    str(natural_output / "model.sysml"), *natural_cases], check=True)

    outputs = [work / "first", work / "second"]
    for output in outputs:
        run("generate", mapping, output, 0)
        manifest = json.loads((output / "manifest.json").read_text())
        check(manifest["complete"] and manifest["targetValidation"] == "accepted", "missing completion evidence")
        check(len(manifest["generatorBinaryDigest"]) == 64, "missing generator identity")
        check(manifest["library"]["descriptorDigest"] == hashlib.sha256(
            (work / "spec/agda2sysml-spec.agda-lib").read_bytes()).hexdigest(), "missing library identity")
        for filename, digest in manifest["artifacts"].items():
            check(hashlib.sha256((output / filename).read_bytes()).hexdigest() == digest,
                  "artifact digest mismatch")
    for artifact in outputs[0].iterdir():
        check(artifact.read_bytes() == (outputs[1] / artifact.name).read_bytes(),
              f"nondeterministic {artifact.name}")
    inventory = json.loads((outputs[0] / "inventory.json").read_text())
    check_source_catalog(inventory)
    definitions = [d for module in inventory["modules"] for d in module["definitions"]]
    negation = next(d for d in definitions if d["displayName"] == "Agda2SysML.Foundation.not")
    check(len(negation["sourceSyntax"]) == 1, "missing source group")
    check(all(c["source"]["start"] is not None for c in negation["sourceSyntax"][0]["clauses"]),
          "missing original clause locations")
    check(all(not Path(module["source"]["path"]).is_absolute() for module in inventory["modules"]),
          "absolute source path leaked")
    roles = inventory["models"]["negation"]
    check(roles["transition"]["entry"]["symbols"] == [negation["name"]], "model role lost its canonical reference")
    report = json.loads((outputs[0] / "correspondence.json").read_text())
    check(report["models"]["negation"]["transitionTargets"], "model has no target correspondence")
    marker = outputs[0] / "keep"
    marker.write_text("existing output")
    run("generate", mapping, outputs[0], 1)
    check(marker.read_text() == "existing output", "output was overwritten")

    original_ids = {d["name"]: d["id"] for d in definitions}
    source_file = work / "spec/Agda2SysML/Foundation.agda"
    source_file.write_text("\n\n" + source_file.read_text())
    run("generate", mapping, work / "shifted-source", 0)
    shifted = json.loads((work / "shifted-source/inventory.json").read_text())
    check_source_catalog(shifted)
    original_catalog_ids = {m["name"]: [o["id"] for o in m["sourceCorrespondence"]["occurrences"]] for m in inventory["modules"]}
    check(original_catalog_ids == {m["name"]: [o["id"] for o in m["sourceCorrespondence"]["occurrences"]] for m in shifted["modules"]},
          "source line movement changed occurrence identities")
    shifted_defs = [d for module in shifted["modules"] for d in module["definitions"]]
    check(original_ids == {d["name"]: d["id"] for d in shifted_defs}, "source line movement changed identities")
    check((work / "shifted-source/model.sysml").read_bytes() == (outputs[0] / "model.sysml").read_bytes(),
          "source line movement changed semantic output")
    shifted_negation = next(d for d in shifted_defs if d["name"] == negation["name"])
    check(shifted_negation["sourceSyntax"] != negation["sourceSyntax"], "moved source used stale source anchors")

    multiple = work / "multiple.yaml"
    multiple.write_text(mapping.read_text().replace("roots: [Agda2SysML.Foundation]",
        "roots: [Agda2SysML.Foundation, Agda2SysML.Relations]"))
    run("inspect", multiple, work / "multiple-roots", 0)
    merged = json.loads((work / "multiple-roots/inventory.json").read_text())
    module_names = [m["name"] for m in merged["modules"]]
    check(len(module_names) == len(set(module_names)) and "Agda2SysML.Relations" in module_names,
          "multiple roots were not merged consistently")

    bad = work / "bad.yaml"
    bad.write_text(mapping.read_text().replace("symbol: not", "symbol: absent"))
    run("inspect", bad, work / "bad-output", 1)
    check(not (work / "bad-output").exists(), "invalid mapping left a bundle")
    bad.write_text(mapping.read_text().replace("position: 0", "position: 7"))
    run("inspect", bad, work / "bad-selector", 1)

    implication = work / "contracts/implication.yaml"
    run("generate", implication, work / "implication", 0)
    implication_manifest = json.loads((work / "implication/manifest.json").read_text())
    implication_report = json.loads((work / "implication/correspondence.json").read_text())
    check(implication_manifest["complete"], "finite relation translation is incomplete")
    check(any(x["rule"] == "native.finite-relation" for x in implication_report["obligations"]),
          "relation native rule is missing")

    run("generate", work / "contracts/witnessed.yaml", work / "witnessed", 0)
    witnessed = json.loads((work / "witnessed/inventory.json").read_text())
    check_source_catalog(witnessed)
    witness_module = next(m for m in witnessed["modules"] if m["name"] == "Witnessed")
    witness_owners = {d["name"] for d in witness_module["definitions"] if d["displayName"] == "Witnessed.Recorded.keep"}
    check(any(o["role"] == "constructor-signature" and o["owner"] in witness_owners
              for o in witness_module["sourceCorrespondence"]["occurrences"]), "constructor signature lacks its checked owner")
    witness_report = json.loads((work / "witnessed/correspondence.json").read_text())
    check(witness_report["complete"] and all(o["status"] == "discharged" for o in witness_report["obligations"]),
          "witnessed relation was not completely translated")
    def witness_expand(value):
        if isinstance(value, dict):
            if set(value) == {"$node"}:
                node = witnessed["nodes"][value["$node"]]
                if "object" in node:
                    return {k: witness_expand(v) for k, v in node["object"].items()}
                return [witness_expand(v) for v in node["array"]]
            return {k: witness_expand(v) for k, v in value.items()}
        if isinstance(value, list):
            return [witness_expand(v) for v in value]
        return value
    witness_defs = {d["displayName"]: d for m in witnessed["modules"] for d in m["definitions"]}
    for name, expected in (("keep", [True, False]), ("overwrite", [False, True, False, True, False]),
                           ("classified", [True, False])):
        ty = witness_expand(witness_defs["Witnessed.Recorded." + name]["type"])
        bindings = []
        while ty["term"]["tag"] == "pi":
            codomain = ty["term"]["codomain"]
            bindings.append(codomain["binds"])
            ty = codomain["body"]
        check(bindings == expected, "compiler contract did not exercise its binding/nonbinding layout")
    expressions = []
    for before, after in itertools.product(("false", "true"), repeat=2):
        for values in itertools.product(("false", "true"), repeat=2):
            expected = before == values[0] and after == values[0]
            expressions += [f"'Witnessed.Recorded.keep'({', '.join((before, after, *values))})", str(expected).lower()]
        for values in itertools.product(("false", "true"), repeat=5):
            expected = before == values[1] and after == values[3]
            expressions += [f"'Witnessed.Recorded.overwrite'({', '.join((before, after, *values))})", str(expected).lower()]
        for value, phase in itertools.product(("false", "true"), ("idle", "active")):
            phase_value = f"'Indexed.Phase'::'Indexed.Phase.{phase}'"
            expected = before == value and after == value
            expressions += [f"'Witnessed.Recorded.classified'({before}, {after}, {value}, {phase_value})", str(expected).lower()]
    subprocess.run([java, "--class-path", str(validator / "jupyter-sysml-kernel-0.58.0-all.jar"),
                    str(repository / "test/TargetEvaluation.java"), str(validator / "sysml.library"),
                    str(work / "witnessed/model.sysml"), *expressions], check=True)

    run("generate", work / "contracts/register.yaml", work / "register", 0)
    register_report = json.loads((work / "register/correspondence.json").read_text())
    register_manifest = json.loads((work / "register/manifest.json").read_text())
    check(register_manifest["complete"] and register_manifest["targetValidation"] == "accepted",
          "record/payload contract is incomplete")
    carriers = register_report["algebraicCarriers"]
    check(sorted(c["kind"] for c in carriers) == ["record", "sum"], "record/sum correspondence missing")
    record_carrier = next(c for c in carriers if c["kind"] == "record")
    check([p["position"] for p in record_carrier["constructors"][0]["payload"]] == [0, 1],
          "record payload positions lost")
    check(all(x["status"] == "discharged" for x in register_report["obligations"]), "unresolved record obligation")
    check(any(x["kind"] == "statement" and "Equality._≡_#" in x["symbol"]
              for x in register_report["obligations"]), "theorem dependency was not retained")
    check(not any(x["kind"] in ("behavior", "structure") and "Equality._≡_#" in x["symbol"]
                  for x in register_report["obligations"]), "retained theorem created an executable equality obligation")
    record_expressions = []
    for value in ("false", "true"):
        for enabled in ("false", "true"):
            record_value = (f"new 'Register.State'('Register.State.value'={value},"
                            f"'Register.State.enabled'={enabled})")
            record_expressions += [f"'Register.State.value'({record_value})", value,
                                   f"'Register.State.enabled'({record_value})", enabled]
            for tag in ("retain", "replace"):
                payload = record_value if tag == "replace" else "null"
                command = (f"new 'Register.Command'('constructor'='Register.Command.constructor-tag'::"
                           f"'Register.Command.{tag}', 'Register.Command.write.payload0'=null, "
                           f"'Register.Command.enable.payload0'=null, 'Register.Command.replace.payload0'={payload})")
                record_expressions += [f"'Register.Command.payload-valid'({command})", "true",
                                       f"'Register.State.value'('Register.step'({command}, {record_value}))", value]
    subprocess.run([java, "--class-path", str(validator / "jupyter-sysml-kernel-0.58.0-all.jar"),
                    str(repository / "test/TargetEvaluation.java"), str(validator / "sysml.library"),
                    str(work / "register/model.sysml"), *record_expressions], check=True)

    run("generate", work / "contracts/register-workflow.yaml", work / "workflow", 0)
    workflow_report = json.loads((work / "workflow/correspondence.json").read_text())
    workflow_manifest = json.loads((work / "workflow/manifest.json").read_text())
    check(workflow_manifest["complete"] and workflow_manifest["targetValidation"] == "accepted",
          "first-order workflow contract is incomplete")
    check(any(x["rule"] == "native.first-order-calls" and "RegisterWorkflow.sequence#" in x["symbol"]
              for x in workflow_report["obligations"]), "native helper-call rule missing")
    dependencies = workflow_report["calculationDependencies"]
    check(len(dependencies) == 1 and len(dependencies[0]["callees"]) == 1,
          "workflow call graph lost or invented a dependency")
    callee = dependencies[0]["callees"][0]
    check("Register.step#" in callee["symbol"] and callee["target"] == "AgdaModel::'Register.step'",
          "helper identity or target correspondence lost")
    check(all(any(x["symbol"] == edge["symbol"] and x["kind"] == "behavior"
                  and x["status"] == "discharged" for x in workflow_report["obligations"])
              for node in dependencies for edge in node["callees"]),
          "caller emitted without a discharged helper body")
    workflow_expressions = []
    retain = ("new 'Register.Command'('constructor'='Register.Command.constructor-tag'::"
              "'Register.Command.retain', 'Register.Command.write.payload0'=null, "
              "'Register.Command.enable.payload0'=null, 'Register.Command.replace.payload0'=null)")
    for value in ("false", "true"):
        for enabled in ("false", "true"):
            state = (f"new 'Register.State'('Register.State.value'={value},"
                     f"'Register.State.enabled'={enabled})")
            sequence = f"'RegisterWorkflow.sequence'({retain}, {retain}, {state})"
            workflow_expressions += [f"'Register.State.value'({sequence})", value,
                                     f"'Register.State.enabled'({sequence})", enabled]
    subprocess.run([java, "--class-path", str(validator / "jupyter-sysml-kernel-0.58.0-all.jar"),
                    str(repository / "test/TargetEvaluation.java"), str(validator / "sysml.library"),
                    str(work / "workflow/model.sysml"), *workflow_expressions], check=True)

    run("generate", work / "contracts/parameterized.yaml", work / "parameterized", 0)
    specialized = json.loads((work / "parameterized/correspondence.json").read_text())
    check(specialized["complete"] and all(o["status"] == "discharged" for o in specialized["obligations"]),
          "concrete type-parameter specialization is incomplete")
    instances = specialized["specializations"]
    check(len(instances) == 18 and len({i["instance"] for i in instances}) == 18,
          "concrete instances missing or duplicated")
    original = json.loads((work / "parameterized/inventory.json").read_text())
    source_symbols = {d["name"] for m in original["modules"] for d in m["definitions"]}
    check(all(i["symbol"] in source_symbols and i["instance"] not in source_symbols for i in instances),
          "specialization replaced the checked source inventory")
    check(all(o["source"]["checkedDefinition"] in source_symbols for o in specialized["obligations"]),
          "specialization source links are not resolvable")
    check(all(i["targets"] for i in instances), "concrete instance lacks a target correspondence")
    for o in specialized["obligations"]:
        if o["rule"] == "native.concrete-instantiations":
            check(o["instances"] and all(any(p["symbol"] == s and p["kind"] == o["kind"]
                  and p["status"] == "discharged" for p in specialized["obligations"]) for s in o["instances"]),
                  "generic obligation discharged without every required concrete instance")
    def instance(name, domain):
        return next(i for i in instances if i["symbol"].startswith(name + "#")
                    and i["arguments"][0]["symbol"].startswith(domain + "#"))
    def carrier(name, domain):
        key = instance(name, domain)["instance"]
        return next(c for c in specialized["algebraicCarriers"] if c["symbol"] == key)
    specialized_expressions = []
    for domain, values in (("Agda.Builtin.Bool.Bool", ("false", "true")),
                           ("Parameterized.Colour", ("'Parameterized.Colour'::'Parameterized.Colour.red'",
                                                      "'Parameterized.Colour'::'Parameterized.Colour.blue'"))):
        box = carrier("Parameterized.Box", domain)
        choice = carrier("Parameterized.Choice", domain)
        field = box["constructors"][0]["payload"][0]["target"].rsplit("::", 1)[1]
        retain = instance("Parameterized.retain", domain)["targets"][0]
        choose = instance("Parameterized.choose", domain)["targets"][0]
        tag_type = choice["target"][:-1] + ".constructor-tag'"
        for value in values:
            boxed = f"new {box['target']}({field}={value})"
            specialized_expressions += [f"({retain}({boxed})).{field} == {value}", "true"]
            for selected in choice["constructors"]:
                tag = selected["target"].rsplit("::", 1)[1]
                fields = [f"{c['payload'][0]['target'].rsplit('::', 1)[1]}="
                          + (value if c == selected else "null") for c in choice["constructors"]]
                selected_value = f"new {choice['target']}('constructor'={tag_type}::{tag}, " + ", ".join(fields) + ")"
                specialized_expressions += [f"{choose}({selected_value}) == {value}", "true"]
    subprocess.run([java, "--class-path", str(validator / "jupyter-sysml-kernel-0.58.0-all.jar"),
                    str(repository / "test/TargetEvaluation.java"), str(validator / "sysml.library"),
                    str(work / "parameterized/model.sysml"), *specialized_expressions], check=True)
    run("generate", work / "contracts/universe-polymorphic.yaml", work / "universes", 0)
    universes = json.loads((work / "universes/correspondence.json").read_text())
    source = json.loads((work / "universes/inventory.json").read_text())
    source_symbols = {d["name"] for m in source["modules"] for d in m["definitions"]}
    instances = universes["specializations"]
    check(universes["complete"] and all(o["status"] == "discharged" for o in universes["obligations"]),
          "universe-polymorphic generation is incomplete")
    check(len(instances) == 13 and len({i["instance"] for i in instances}) == 13,
          "universe instances missing or duplicated")
    check(all(i["symbol"] in source_symbols and i["instance"] not in source_symbols for i in instances),
          "universe specialization changed original inventory")
    check(all(o["source"]["checkedDefinition"] in source_symbols for o in universes["obligations"]),
          "universe instance lost its checked source")
    def level_instance(name, value):
        return next(i for i in instances if i["symbol"].startswith("UniversePolymorphic." + name + "#")
                    and i["arguments"][0] == {"level": value})
    def level_carrier(name, value):
        key = level_instance(name, value)["instance"]
        return next(c for c in universes["algebraicCarriers"] if c["symbol"] == key)
    def field_of(c):
        return c["constructors"][0]["payload"][0]["target"].rsplit("::", 1)[1]
    box0, box2, lift = level_carrier("Box", 0), level_carrier("Box", 2), level_carrier("Lift", 0)
    enclose = level_instance("enclose", 0)
    check(enclose["arguments"][:3] == [{"level": 0}, {"level": 1}, {"level": 2}],
          "ordered level arguments were lost")
    static = [o for o in universes["obligations"] if o["rule"] == "static.universe-level"]
    level_symbols = {source["builtins"][k] for k in ("level", "levelUniverse", "levelZero", "levelSuc", "levelMax")}
    check(static and all(o["symbol"] in level_symbols and o["target"] is None for o in static),
          "level metadata was represented by a runtime target")
    check(not any(c["symbol"] in level_symbols for c in universes["algebraicCarriers"]),
          "runtime universe carrier emitted")
    model = (work / "universes/model.sysml").read_text()
    check("'UniversePolymorphic.step'::'input0'" in model,
          "nested constructor inputs lost their calculation scope")
    level_expressions = []
    for value in ("false", "true"):
        ordinary = f"new {box0['target']}({field_of(box0)}={value})"
        raised = f"new {box2['target']}({field_of(box2)}=new {lift['target']}({field_of(lift)}={value}))"
        state = (f"new 'UniversePolymorphic.State'('UniversePolymorphic.State.ordinary'={ordinary},"
                 f"'UniversePolymorphic.State.raised'={raised})")
        level_expressions += [f"'UniversePolymorphic.readOrdinary'({state})", value,
                              f"'UniversePolymorphic.readRaised'({state})", value]
        for n, carrier_value, carrier in ((0, ordinary, box0), (2, raised, box2)):
            identity = level_instance("identity", n)["targets"][0]
            projected = f"({identity}({carrier_value})).{field_of(carrier)}"
            if n == 2:
                projected = f"({projected}).{field_of(lift)}"
            level_expressions += [projected, value]
        retain = level_instance("retain", 0)["targets"][0]
        level_expressions += [f"({retain}({ordinary})).{field_of(box0)}", value]
    subprocess.run([java, "--class-path", str(validator / "jupyter-sysml-kernel-0.58.0-all.jar"),
                    str(repository / "test/TargetEvaluation.java"), str(validator / "sysml.library"),
                    str(work / "universes/model.sysml"), *level_expressions], check=True)

    run("generate", work / "contracts/indexed.yaml", work / "indexed", 0)
    indexed = json.loads((work / "indexed/correspondence.json").read_text())
    check(indexed["complete"] and all(o["status"] == "discharged" for o in indexed["obligations"]),
          "finite indexed families did not generate completely")
    carriers = indexed["algebraicCarriers"]
    permit = next(c for c in carriers if c["symbol"].startswith("Indexed.Permit#"))
    flag_family = next(c for c in carriers if c["symbol"].startswith("Indexed.Flagged#"))
    state_family = next(c for c in carriers if c["symbol"].startswith("Indexed.State#"))
    check(len(permit["indices"]) == len(flag_family["indices"]) == 1, "index domains missing")
    check(all(c["resultIndices"] for c in permit["constructors"] + flag_family["constructors"]),
          "constructor/index correspondence missing")
    check(all(f["refinements"] for f in state_family["constructors"][0]["payload"]),
          "record field fibre constraint missing")
    check(any(c["symbol"].startswith("Indexed.retain#") and len(c["constraints"]) == 2
              for c in indexed["indexContracts"]), "dependent calculation input/result constraints missing")
    result_trace, _ = check_target_trace(work / "indexed")
    result_roots = {(r["owner"], r["root"]): r["value"] for r in result_trace["checkedRoots"]}
    result_checked = {r["id"]: r for r in result_trace["checkedOccurrences"]}
    result_derivations = {d["id"]: d for d in result_trace["derivations"]}
    for prefix, kind, constant in (("Indexed.Permit.waiting#", "enumeration", "Indexed.Phase.idle#"),
                                   ("Indexed.Permit.granted#", "enumeration", "Indexed.Phase.active#"),
                                   ("Indexed.Flagged.flagged#", "input", None)):
        targets = [t for t in result_trace["targetOccurrences"] if t["owner"].startswith(prefix)]
        contracts = [t for t in targets if t["role"] == "index-contract"]
        check(len(contracts) == 1 and contracts[0]["sourcePrecision"] == "derived",
              "simple constructor result assertion lost its source derivation")
        target = contracts[0]
        owner = target["owner"]
        derivation = result_derivations[target["derivation"]]
        evidence, premises = derivation["evidence"], derivation["evidence"]["premises"]
        check(evidence["rule"] == "native.constructor-result-index" and premises["kind"] == kind
              and premises["constructor"] == owner and premises["index"] == 0
              and premises["indexField"] == premises["family"] + ".index0",
              "constructor result assertion lost its family/index identity")
        ty, result_path, domains = result_roots[owner, "type"], [], []
        while ty["term"]["tag"] == "pi":
            term = ty["term"]
            domains.append((result_path + ["term", "domain", "type"], term["codomain"]["binds"]))
            result_path += ["term", "codomain", "body"]
            ty = term["codomain"]["body"]
        check(ty["term"]["symbol"] == premises["family"], "result family differs from checked terminal type")
        value_path = result_path + ["term", "eliminations", 0, "argument", "value"]
        value = ty["term"]["eliminations"][0]["argument"]["value"]
        slots = list(reversed([i for i, (_, binds) in enumerate(domains) if binds]))
        expected_paths = {(), tuple(result_path), tuple(value_path)}
        check(premises["bindingSlots"] == slots and not value["eliminations"],
              "result assertion lost its exact terminal index form or binder context")
        if kind == "input":
            slot = premises["expectedInput"]
            check(value["tag"] == "variable" and slots[value["index"]] == slot == 0,
                  "constructor result guessed its input position")
            expected_paths.add(tuple(domains[slot][0]))
        else:
            check(value["tag"] == "constructor" and value["symbol"] == premises["valueConstructor"]
                  and premises["valueConstructor"].startswith(constant)
                  and premises["valueFamily"].startswith("Indexed.Phase#"),
                  "constructor result changed its finite value identity")
        refs = [result_checked[r] for r in derivation["inputs"]]
        check(all(r["owner"] == owner and r["root"] == "type" for r in refs)
              and {tuple(r["path"]) for r in refs} == expected_paths,
              "result assertion lacks its terminal type/index and input occurrence evidence")
        check(not any(t["role"] == "index-contract-boundary" for t in targets),
              "supported constructor result assertion retains a boundary")
        check(all(t["sourcePrecision"] == "derived" for t in targets),
              "supported result assertion did not complete the already-derived constructor helper")
    check(any(t["owner"].startswith("Indexed.approve#") and t["role"] == "index-contract-boundary"
              for t in result_trace["targetOccurrences"]), "constructor rule escaped into ordinary function contracts")
    expressions = []
    def permit_value(tag, phase, value, approved="true"):
        return ("new 'Indexed.Permit'('constructor'='Indexed.Permit.constructor-tag'::'Indexed.Permit."
                + tag + "', 'Indexed.Permit.index0'='Indexed.Phase'::'Indexed.Phase." + phase
                + "', 'Indexed.Permit.waiting.payload0'=" + (value if tag == "waiting" else "null")
                + ", 'Indexed.Permit.granted.payload0'=" + (value if tag == "granted" else "null")
                + ", 'Indexed.Permit.granted.payload1'=" + (approved if tag == "granted" else "null") + ")")
    def flag_value(index, payload):
        return ("new 'Indexed.Flagged'('constructor'='Indexed.Flagged.constructor-tag'::"
                "'Indexed.Flagged.flagged', 'Indexed.Flagged.index0'=" + index
                + ", 'Indexed.Flagged.flagged.payload0'=" + payload + ")")
    for value in ("false", "true"):
        waiting = permit_value("waiting", "idle", value)
        granted = permit_value("granted", "active", value)
        for tag, phase, datum in (("waiting", "idle", waiting), ("granted", "active", granted)):
            other = "active" if phase == "idle" else "idle"
            expressions += [f"'Indexed.Permit.payload-valid'({datum})", "true",
                            f"'Indexed.Permit.payload-valid'({permit_value(tag, other, value)})", "false",
                            f"'Indexed.read'('Indexed.Phase'::'Indexed.Phase.{phase}', {datum})", value,
                            f"'Indexed.read'('Indexed.Phase'::'Indexed.Phase.{phase}', "
                            f"'Indexed.retain'('Indexed.Phase'::'Indexed.Phase.{phase}', {datum}))", value]
        expressions += [f"'Indexed.Flagged.payload-valid'({flag_value(value, value)})", "true",
                        f"'Indexed.Flagged.payload-valid'({flag_value(value, 'true' if value == 'false' else 'false')})", "false",
                        f"'Indexed.flag'({value}, {flag_value(value, value)})", value]
        marked = flag_value("true", "true")
        state = (f"new 'Indexed.State'('Indexed.State.pending'={waiting},"
                 f"'Indexed.State.ready'={granted}, 'Indexed.State.marked'={marked})")
        wrong_state = (f"new 'Indexed.State'('Indexed.State.pending'={granted},"
                       f"'Indexed.State.ready'={waiting}, 'Indexed.State.marked'={marked})")
        expressions += [f"'Indexed.State.payload-valid'({state})", "true",
                        f"'Indexed.State.payload-valid'({wrong_state})", "false",
                        f"'Indexed.readPending'({state})", value, f"'Indexed.readReady'({state})", value,
                        f"'Indexed.readMarked'({state})", "true"]
    subprocess.run([java, "--class-path", str(validator / "jupyter-sysml-kernel-0.58.0-all.jar"),
                    str(repository / "test/TargetEvaluation.java"), str(validator / "sysml.library"),
                    str(work / "indexed/model.sysml"), *expressions], check=True)

    run("generate", work / "contracts/dependent-record.yaml", work / "dependent-record", 0)
    dependent = json.loads((work / "dependent-record/correspondence.json").read_text())
    check(dependent["complete"] and all(o["status"] == "discharged" for o in dependent["obligations"]),
          "dependent record translation is incomplete")
    packet = next(c for c in dependent["algebraicCarriers"] if c["symbol"].startswith("DependentRecord.Packet#"))
    fields = packet["constructors"][0]["payload"]
    check([f["position"] for f in fields] == [0, 1, 2, 3] and fields[1]["refinements"] and fields[3]["refinements"],
          "dependent record lost its ordered prefix relationships")
    check("Packet.phase" in fields[1]["refinements"][0] and "Packet.enabled" in fields[3]["refinements"][0],
          "dependent field refers to another prefix position")
    check(any(c["symbol"].startswith("DependentRecord.packet#") and len(c["constraints"]) == 2
              for c in dependent["indexContracts"]), "dependent constructor input constraints missing")
    check(any(c["symbol"].startswith("DependentRecord.select#") and "Packet.phase" in c["constraints"][0]
              for c in dependent["indexContracts"]), "receiver-specific result constraint missing")
    def packet_value(phase, member, enabled, marker):
        return (f"new 'DependentRecord.Packet'('DependentRecord.Packet.phase'='Indexed.Phase'::'Indexed.Phase.{phase}',"
                f"'DependentRecord.Packet.permit'={member}, 'DependentRecord.Packet.enabled'={enabled},"
                f"'DependentRecord.Packet.marker'={marker})")
    expressions = []
    for phase, tag in (("idle", "waiting"), ("active", "granted")):
        for value in ("false", "true"):
            for enabled in ("false", "true"):
                member = permit_value(tag, phase, value)
                marker = flag_value(enabled, enabled)
                data = packet_value(phase, member, enabled, marker)
                wrong_phase = packet_value("active" if phase == "idle" else "idle", member, enabled, marker)
                wrong_flag = packet_value(phase, member, "true" if enabled == "false" else "false", marker)
                expressions += [f"'DependentRecord.Packet.payload-valid'({data})", "true",
                                f"'DependentRecord.Packet.payload-valid'({wrong_phase})", "false",
                                f"'DependentRecord.Packet.payload-valid'({wrong_flag})", "false",
                                f"'DependentRecord.readPermit'({data})", value,
                                f"'DependentRecord.readMarker'({data})", enabled,
                                f"'Indexed.read'('Indexed.Phase'::'Indexed.Phase.{phase}', 'DependentRecord.select'({data}))", value]
    subprocess.run([java, "--class-path", str(validator / "jupyter-sysml-kernel-0.58.0-all.jar"),
                    str(repository / "test/TargetEvaluation.java"), str(validator / "sysml.library"),
                    str(work / "dependent-record/model.sysml"), *expressions], check=True)

    run("generate", work / "contracts/specialized-indexed.yaml", work / "specialized-indexed", 0)
    composed = json.loads((work / "specialized-indexed/correspondence.json").read_text())
    check(composed["complete"] and all(o["status"] == "discharged" for o in composed["obligations"]),
          "combined static specialization and dependent fields are incomplete")
    instances = composed["specializations"]
    def composed_instance(name, level):
        return next(i for i in instances if i["symbol"].startswith("SpecializedIndexed." + name + "#")
                    and i["arguments"][0] == {"level": level})
    def composed_carrier(name, level):
        key = composed_instance(name, level)["instance"]
        return next(c for c in composed["algebraicCarriers"] if c["symbol"] == key)
    for family in ("Evidence", "Permit", "Packet"):
        check(len([i for i in instances if i["symbol"].startswith("SpecializedIndexed." + family + "#")]) == 2,
              "runtime indices split or collapsed concrete payload specializations")
    for level in (0, 1):
        packet = composed_carrier("Packet", level)
        fields = packet["constructors"][0]["payload"]
        check([f["position"] for f in fields] == [0, 1, 2, 3]
              and "Packet.enabled" in fields[1]["refinements"][0]
              and "Packet.phase" in fields[3]["refinements"][0],
              "specialization changed ordered dependent field references")
        retaining = composed_instance("retain", level)["instance"]
        check(any(c["symbol"] == retaining and len(c["constraints"]) == 2 for c in composed["indexContracts"]),
              "omitted runtime index disappeared with static parameters")
    boxes = [c for c in composed["algebraicCarriers"] if c["symbol"].startswith("UniversePolymorphic.Box#")]
    check(len(boxes) == 2 and len({c["target"] for c in boxes}) == 2,
          "different fixed fibres used as static arguments have colliding targets")
    def fixed_box(index):
        return next(c for c in boxes if f"== {index})" in c["constructors"][0]["payload"][0]["refinements"][0])
    raised_carrier = next(c for c in composed["algebraicCarriers"] if c["symbol"].startswith("UniversePolymorphic.Lift#"))
    def record_value(carrier, values):
        fields = carrier["constructors"][0]["payload"]
        check(len(fields) == len(values), "record evaluation input has wrong arity")
        args = ", ".join(f"{f['target'].rsplit('::', 1)[1]}={v}" for f, v in zip(fields, values))
        return f"new {carrier['target']}({args})"
    def indexed_value(carrier, selected, index, value):
        local = carrier["target"].rsplit("::", 1)[1]
        tag_type = "AgdaModel::" + local[:-1] + ".constructor-tag'"
        constructor = next(c for c in carrier["constructors"] if c["symbol"].split("#")[0].endswith("." + selected))
        tag_value = constructor["target"].rsplit("::", 1)[1]
        args = [f"'constructor'={tag_type}::{tag_value}",
                f"{carrier['indices'][0]['target'].rsplit('::', 1)[1]}={index}"]
        for c in carrier["constructors"]:
            args += [f"{f['target'].rsplit('::', 1)[1]}={value if c == constructor else 'null'}" for f in c["payload"]]
        return f"new {carrier['target']}({', '.join(args)})"
    expressions = []
    for enabled in ("false", "true"):
        for phase, permit_tag in (("idle", "waiting"), ("active", "granted")):
            phase_value = f"'Indexed.Phase'::'Indexed.Phase.{phase}'"
            other_phase = "'Indexed.Phase'::'Indexed.Phase." + ("active" if phase == "idle" else "idle") + "'"
            for value in ("false", "true"):
                packets = []
                members = []
                for level in (0, 1):
                    payload = value if level == 0 else record_value(raised_carrier, [value])
                    evidence = indexed_value(composed_carrier("Evidence", level),
                                             "on" if enabled == "true" else "off", enabled, payload)
                    permit = indexed_value(composed_carrier("Permit", level), permit_tag, phase_value, payload)
                    carrier = composed_carrier("Packet", level)
                    packet = record_value(carrier, [enabled, evidence, phase_value, permit])
                    wrong_flag = record_value(carrier, ["true" if enabled == "false" else "false", evidence, phase_value, permit])
                    wrong_phase = record_value(carrier, [enabled, evidence, other_phase, permit])
                    expressions += [f"{carrier['admissibility']}({packet})", "true",
                                    f"{carrier['admissibility']}({wrong_flag})", "false",
                                    f"{carrier['admissibility']}({wrong_phase})", "false"]
                    packets.append(packet)
                    members.append(evidence)
                off = indexed_value(composed_carrier("Evidence", 0), "off", "false", value)
                on = indexed_value(composed_carrier("Evidence", 0), "on", "true", value)
                wrapped = record_value(fixed_box("false"), [off])
                wrapped_true = record_value(fixed_box("true"), [on])
                state = (f"new 'SpecializedIndexed.State'('SpecializedIndexed.State.ordinary'={packets[0]},"
                         f"'SpecializedIndexed.State.raised'={packets[1]},'SpecializedIndexed.State.wrapped'={wrapped},"
                         f"'SpecializedIndexed.State.wrappedTrue'={wrapped_true})")
                for read in ("readOrdinary", "readRaised", "readWrapped", "readWrappedTrue"):
                    expressions += [f"'SpecializedIndexed.{read}'({state})", value]
                retain = composed_instance("retain", 0)["targets"][0]
                read = composed_instance("read", 0)["targets"][0]
                expressions += [f"{read}({enabled}, {retain}({enabled}, {members[0]}))", value]
    subprocess.run([java, "--class-path", str(validator / "jupyter-sysml-kernel-0.58.0-all.jar"),
                    str(repository / "test/TargetEvaluation.java"), str(validator / "sysml.library"),
                    str(work / "specialized-indexed/model.sysml"), *expressions], check=True)

    run("generate", work / "contracts/dependent-payload.yaml", work / "dependent-payload", 0)
    dependent_payload = json.loads((work / "dependent-payload/correspondence.json").read_text())
    trace, trace_values = check_target_trace(work / "dependent-payload")
    trace_derivations = {d["id"]: d for d in trace["derivations"]}
    read_sites = []
    for target in trace["targetOccurrences"]:
        if target["owner"].startswith("DependentPayload.observe#") and target["role"] == "call":
            inputs = trace_derivations[target["derivation"]]["inputs"]
            read_sites += [(target["id"], i) for i in inputs if trace_values[i].get("symbol", "").startswith("Indexed.read#")]
    check(len(read_sites) == 2 and len({t for t, _ in read_sites}) == 2 and len({c for _, c in read_sites}) == 2,
          "repeated read calls collapsed target or checked occurrence identity")
    payload_inventory = json.loads((work / "dependent-payload/inventory.json").read_text())
    payload_module = next(m for m in payload_inventory["modules"] if m["name"] == "DependentPayload")
    payload_alignment = payload_module["sourceAlignment"]["definitions"]
    copy_alignment = next(d for d in payload_alignment if d["owner"].startswith("DependentPayload.copy#"))
    check(copy_alignment["unavailable"] is None and len({l["clause"] for l in copy_alignment["links"]}) == 4,
          "constructor payload clauses lost binding evidence")
    payload_trace, _ = check_target_trace(work / "dependent-payload")
    copy_targets = [t for t in payload_trace["targetOccurrences"] if t["owner"].startswith("DependentPayload.copy#")]
    copy_projections = [t for t in copy_targets if t["role"] == "projection"]
    check(copy_projections and all(t["sourcePrecision"] == "derived" for t in copy_projections), "direct payload projections lost clause chains")
    copy_constructions = [t for t in copy_targets if t["role"] == "construction"]
    check(len(copy_constructions) == 4 and all(t["sourcePrecision"] == "derived" for t in copy_targets),
          "verified projection signature did not complete copy provenance")
    payload_signatures = next(m for m in payload_inventory["modules"] if m["name"] == "DependentPayload")["sourceAlignment"]["signatures"]
    event_signatures = {d["owner"].split("#")[0].rsplit(".", 1)[1]: d
                        for d in payload_signatures if d["owner"].startswith("DependentPayload.Event.")}
    check(all(event_signatures[c]["unavailable"] is None for c in ("quiet", "marked", "authorized")),
          "explicit constructor telescope lost source evidence")
    check(event_signatures["embedded"]["unavailable"] is None and event_signatures["embedded"]["links"],
          "explicit projection constructor signature lost checked evidence")
    hidden_signatures = [d for d in payload_signatures if d["owner"].startswith("DependentPayload.Envelope.")]
    check(hidden_signatures and all(d["unavailable"] is not None and not d["links"] for d in hidden_signatures),
          "projection signature rule admitted hidden parameter elaboration")
    payload_derivations = {d["id"]: d for d in payload_trace["derivations"]}
    payload_checked = {c["id"]: c for c in payload_trace["checkedOccurrences"]}
    representation = []
    for target in copy_targets:
        if target["role"] != "value":
            continue
        evidence = payload_derivations[target["derivation"]]["evidence"]
        if evidence["rule"] not in ("native.constructor-tag", "native.inactive-payload"):
            continue
        representation.append(target)
        premises = evidence["premises"]
        selected = premises["selectedConstructor"]
        schema_owners = {selected}
        if evidence["rule"] == "native.inactive-payload":
            slot_owner = premises["slotConstructor"]
            check(slot_owner != selected and premises["position"] >= 0
                  and premises["field"] == slot_owner + ".payload" + str(premises["position"]),
                  "inactive slot lost canonical owner or ordered position")
            schema_owners.add(slot_owner)
        inputs = [payload_checked[i] for i in payload_derivations[target["derivation"]]["inputs"]]
        check({c["owner"] for c in inputs if c["root"] == "type" and c["path"] == []} == schema_owners,
              "representation value lacks its checked constructor schemas")
        check(any(c["owner"] == target["owner"] and c["root"] == "compiled" for c in inputs),
              "representation value lost the constructor application occurrence")
        check(target["sourcePrecision"] == "derived", "aligned representation value lacks a source chain")
    check(len(representation) == 31 and all(t["sourcePrecision"] == "derived" for t in representation),
          "constructor tag/padding derivations missing")
    # Generated constructor inputs cite real telescope domains, not guessed
    # source variables or an equal domain found elsewhere in the signature.
    helper_roots = {(r["owner"], r["root"]): r["value"] for r in payload_trace["checkedRoots"]}
    for constructor, arity in (("quiet", 1), ("marked", 2), ("authorized", 4), ("embedded", 2)):
        owner = event_signatures[constructor]["owner"]
        targets = [t for t in payload_trace["targetOccurrences"] if t["owner"] == owner]
        helper_inputs = [t for t in targets if t["role"] == "input"]
        check(len(helper_inputs) == arity and all(t["sourcePrecision"] == "derived" for t in helper_inputs),
              "constructor helper lost a declared input origin")
        ty, path, domains = helper_roots[owner, "type"], [], []
        while ty["term"]["tag"] == "pi":
            term = ty["term"]
            domains.append((path + ["term", "domain", "type"], term["codomain"]["binds"]))
            path += ["term", "codomain", "body"]
            ty = term["codomain"]["body"]
        check(len(domains) == arity, "constructor helper input arity differs from checked telescope")
        for i, target in enumerate(helper_inputs):
            derivation = payload_derivations[target["derivation"]]
            evidence = derivation["evidence"]
            check(evidence["rule"] == "native.constructor-input"
                  and evidence["premises"]["position"] == i
                  and evidence["premises"]["binds"] == domains[i][1]
                  and evidence["premises"]["field"] == owner + ".payload" + str(i),
                  "constructor helper input has the wrong slot identity")
            refs = [payload_checked[r] for r in derivation["inputs"]]
            check(all(r["owner"] == owner and r["root"] == "type" for r in refs)
                  and {tuple(r["path"]) for r in refs} == {(), tuple(domains[i][0])},
                  "constructor helper input lacks its exact domain and complete schema")
        helper_bodies = [t for t in targets if t["role"] == "construction"]
        check(len(helper_bodies) == 1 and helper_bodies[0]["sourcePrecision"] == "derived"
              and payload_derivations[helper_bodies[0]["derivation"]]["evidence"]["rule"] == "native.constructor-helper",
              "constructor helper body lost its schema derivation")
        contracts = [t for t in targets if t["role"] == "index-contract-boundary"]
        check(not contracts, "supported constructor input contract retains a boundary")
        direct_contracts = [t for t in targets if t["role"] == "index-contract"]
        expected_contracts = {"quiet": [], "marked": [(1, 0)], "authorized": [(1, 0), (3, 2)], "embedded": [(1, 0)]}[constructor]
        check(len(direct_contracts) == len(expected_contracts), "constructor input-index contract coverage differs")
        for target, (input_position, expected_input) in zip(direct_contracts, expected_contracts):
            derivation = payload_derivations[target["derivation"]]
            evidence, premises = derivation["evidence"], derivation["evidence"]["premises"]
            expected_rule = "native.constructor-projected-input-index" if constructor == "embedded" else "native.constructor-input-index"
            check(target["sourcePrecision"] == "derived" and evidence["rule"] == expected_rule
                  and premises["input"] == input_position and premises["expectedInput"] == expected_input
                  and premises["index"] == 0 and premises["indexField"] == premises["family"] + ".index0",
                  "input contract lost its dependent input, expected input, or family index")
            variable_path = domains[input_position][0] + ["term", "eliminations", 0, "argument", "value"]
            refs = [payload_checked[r] for r in derivation["inputs"]]
            check(all(r["owner"] == owner and r["root"] == "type" for r in refs)
                  and {tuple(r["path"]) for r in refs} == {(), tuple(domains[input_position][0]),
                      tuple(domains[expected_input][0]), tuple(variable_path)},
                  "input contract evidence does not cite the actual source-domain and variable occurrences")
            value = helper_roots[owner, "type"]
            for part in variable_path:
                value = value[part]
            context_slots = list(reversed([i for i in range(input_position) if domains[i][1]]))
            check(value["tag"] == "variable"
                  and premises["bindingSlots"] == context_slots and context_slots[value["index"]] == expected_input,
                  "input contract guessed the receiver from a raw de Bruijn index")
            if constructor == "embedded":
                check(value["eliminations"] == [{"tag": "project", "symbol": premises["projection"]}]
                      and premises["projection"].startswith("DependentRecord.Packet.phase#")
                      and premises["record"].startswith("DependentRecord.Packet#"),
                      "projected input contract lost its canonical field or record identity")
                receiver_type = helper_roots[owner, "type"]
                for part in domains[expected_input][0]:
                    receiver_type = receiver_type[part]
                check(receiver_type["term"] == {"tag": "definition", "symbol": premises["record"], "eliminations": []},
                      "projected input contract uses a different receiver type")
            else:
                check(value["eliminations"] == [], "simple input contract gained unchecked eliminations")
        calculations = [t for t in targets if t["role"] == "calculation"]
        check(len(calculations) == 1 and calculations[0]["sourcePrecision"] == ("unavailable" if contracts else "derived"),
              "constructor helper calculation ignored remaining index contracts")
    state_helper = [t for t in payload_trace["targetOccurrences"]
                    if t["owner"].startswith("DependentPayload.state#") and t["role"] == "construction"]
    check(state_helper and all(t["sourcePrecision"] == "unavailable" for t in state_helper),
          "record constructor name became full helper source evidence")
    observe_alignment = next(d for d in payload_alignment if d["owner"].startswith("DependentPayload.observe#"))
    check(observe_alignment["unavailable"] is not None and not observe_alignment["links"],
          "implicit elaboration produced unsupported exact source links")

    check(dependent_payload["complete"] and all(o["status"] == "discharged" for o in dependent_payload["obligations"]),
          "dependent constructor payloads did not generate completely")
    event_carrier = next(c for c in dependent_payload["algebraicCarriers"] if c["symbol"].startswith("DependentPayload.Event#"))
    by_variant = {c["symbol"].split("#")[0].rsplit(".", 1)[1]: c for c in event_carrier["constructors"]}
    check([f["position"] for f in by_variant["authorized"]["payload"]] == [0, 1, 2, 3]
          and "authorized.payload0" in by_variant["authorized"]["payload"][1]["refinements"][0]
          and "authorized.payload2" in by_variant["authorized"]["payload"][3]["refinements"][0],
          "dependent sum payload correspondence lost constructor-local positions")
    check("Packet.phase" in by_variant["embedded"]["payload"][1]["refinements"][0],
          "dependent sum lost index projection from an earlier record payload")
    def payload_instance(name, level):
        return next(i for i in dependent_payload["specializations"]
                    if i["symbol"].startswith(name + "#") and i["arguments"][0] == {"level": level})
    def payload_carrier(name, level):
        key = payload_instance(name, level)["instance"]
        return next(c for c in dependent_payload["algebraicCarriers"] if c["symbol"] == key)
    def sum_value(carrier, selected, values, indices=(), extra=None):
        local = carrier["target"].rsplit("::", 1)[1]
        tag_type = "AgdaModel::" + local[:-1] + ".constructor-tag'"
        constructor = next(c for c in carrier["constructors"] if c["symbol"].split("#")[0].endswith("." + selected))
        check(len(constructor["payload"]) == len(values), "sum evaluation input has wrong arity")
        args = {"'constructor'": f"{tag_type}::{constructor['target'].rsplit('::', 1)[1]}"}
        for c in carrier["constructors"]:
            for i, f in enumerate(c["payload"]):
                args[f["target"].rsplit("::", 1)[1]] = values[i] if c == constructor else "null"
        check(len(indices) == len(carrier["indices"]), "sum evaluation has wrong index arity")
        args.update({i["target"].rsplit("::", 1)[1]: value for i, value in zip(carrier["indices"], indices)})
        args.update(extra or {})
        return f"new {carrier['target']}({', '.join(f'{name}={value}' for name, value in args.items())})"
    expressions = []
    for value in ("false", "true"):
        quiet = sum_value(event_carrier, "quiet", [value])
        missing = sum_value(event_carrier, "quiet", ["null"])
        inactive = sum_value(event_carrier, "quiet", [value], extra={"'DependentPayload.Event.marked.payload0'": "true"})
        expressions += [f"{event_carrier['admissibility']}({quiet})", "true",
                        f"{event_carrier['admissibility']}({missing})", "false",
                        f"{event_carrier['admissibility']}({inactive})", "false"]
        for read in ("observe", "matched"):
            expressions += [f"'DependentPayload.{read}'({quiet})", value]
        for enabled in ("false", "true"):
            marker = flag_value(enabled, enabled)
            marked = sum_value(event_carrier, "marked", [enabled, marker])
            wrong_marked = sum_value(event_carrier, "marked", ["true" if enabled == "false" else "false", marker])
            expressions += [f"{event_carrier['admissibility']}({marked})", "true",
                            f"{event_carrier['admissibility']}({wrong_marked})", "false"]
            for read in ("observe", "matched"):
                expressions += [f"'DependentPayload.{read}'({marked})", enabled]
            for phase, tag in (("idle", "waiting"), ("active", "granted")):
                phase_value = f"'Indexed.Phase'::'Indexed.Phase.{phase}'"
                other = "active" if phase == "idle" else "idle"
                other_phase = f"'Indexed.Phase'::'Indexed.Phase.{other}'"
                permit = permit_value(tag, phase, value)
                authorized = sum_value(event_carrier, "authorized", [phase_value, permit, enabled, marker])
                wrong_phase = sum_value(event_carrier, "authorized", [other_phase, permit, enabled, marker])
                wrong_flag = sum_value(event_carrier, "authorized", [phase_value, permit, "true" if enabled == "false" else "false", marker])
                prefix = packet_value(phase, permit, enabled, marker)
                embedded = sum_value(event_carrier, "embedded", [prefix, permit])
                wrong_embedded = sum_value(event_carrier, "embedded", [packet_value(other, permit_value("granted" if tag == "waiting" else "waiting", other, value), enabled, marker), permit])
                expressions += [f"{event_carrier['admissibility']}({authorized})", "true",
                                f"{event_carrier['admissibility']}({wrong_phase})", "false",
                                f"{event_carrier['admissibility']}({wrong_flag})", "false",
                                f"{event_carrier['admissibility']}({embedded})", "true",
                                f"{event_carrier['admissibility']}({wrong_embedded})", "false"]
                for read in ("observe", "matched"):
                    expressions += [f"'DependentPayload.{read}'({authorized})", value,
                                    f"'DependentPayload.{read}'({embedded})", value]
        for level in (0, 1):
            lift_carrier = payload_carrier("UniversePolymorphic.Lift", 0)
            payload = value if level == 0 else record_value(lift_carrier, [value])
            envelope = payload_carrier("DependentPayload.Envelope", level)
            read = payload_instance("DependentPayload.readEnvelope", level)["targets"][0]
            for enabled in ("false", "true"):
                evidence = indexed_value(payload_carrier("SpecializedIndexed.Evidence", level),
                                         "on" if enabled == "true" else "off", enabled, payload)
                message = sum_value(envelope, "message", [enabled, evidence], [enabled])
                opposite = "true" if enabled == "false" else "false"
                wrong_inner = sum_value(envelope, "message", [opposite, evidence], [opposite])
                wrong_outer = sum_value(envelope, "message", [enabled, evidence], [opposite])
                observed = f"{read}({enabled}, {message})"
                if level == 1:
                    observed = f"({observed}).{field_of(lift_carrier)}"
                expressions += [f"{envelope['admissibility']}({message})", "true",
                                f"{envelope['admissibility']}({wrong_inner})", "false",
                                f"{envelope['admissibility']}({wrong_outer})", "false", observed, value]
            plain = sum_value(envelope, "plain", [payload], ["false"])
            wrong_plain = sum_value(envelope, "plain", [payload], ["true"])
            observed = f"{read}(false, {plain})"
            if level == 1:
                observed = f"({observed}).{field_of(lift_carrier)}"
            expressions += [f"{envelope['admissibility']}({plain})", "true",
                            f"{envelope['admissibility']}({wrong_plain})", "false", observed, value]
    subprocess.run([java, "--class-path", str(validator / "jupyter-sysml-kernel-0.58.0-all.jar"),
                    str(repository / "test/TargetEvaluation.java"), str(validator / "sysml.library"),
                    str(work / "dependent-payload/model.sysml"), *expressions], check=True)

    run("generate", work / "contracts/computed-index.yaml", work / "computed-index", 0)
    computed = json.loads((work / "computed-index/correspondence.json").read_text())
    trace, trace_values = check_target_trace(work / "computed-index")
    nested = [t for t in trace["targetOccurrences"] if t["owner"].startswith("ComputedIndex.nextPhase#") and t["role"] == "call"]
    check(len(nested) == 2, "nested calls lost distinct target occurrences")
    check(all(t["sourcePrecision"] == "derived" for t in nested), "nested calls have incomplete source-to-target chains")
    trace_derivations = {d["id"]: d for d in trace["derivations"]}
    callees = []
    for target in nested:
        derivation = trace_derivations[target["derivation"]]
        callee = derivation["evidence"]["premises"]["callee"]
        checked_calls = [trace_values[i] for i in derivation["inputs"] if trace_values[i].get("tag") == "definition" and trace_values[i].get("symbol") == callee]
        check(len(checked_calls) == 1, "call site was replaced by a callee body origin")
        callees.append(callee.split("#")[0])
    check(callees == ["ComputedIndex.phaseOf", "ComputedIndex.invert"], "nested call origins were swapped")
    computed_inventory = json.loads((work / "computed-index/inventory.json").read_text())
    computed_module = next(m for m in computed_inventory["modules"] if m["name"] == "ComputedIndex")
    source_bytes = computed_module["sourceText"].encode()
    source_occurrences = {o["id"]: o for o in computed_module["sourceCorrespondence"]["occurrences"]}
    def source_slice(source_id):
        return b"".join(source_bytes[i["start"]:i["end"]] for i in source_occurrences[source_id]["intervals"]).decode()
    checked_occurrences = {c["id"]: c for c in trace["checkedOccurrences"]}
    for target in nested:
        derivation = trace_derivations[target["derivation"]]
        callee = derivation["evidence"]["premises"]["callee"]
        call = next(checked_occurrences[i] for i in derivation["inputs"] if trace_values[i].get("symbol") == callee)
        # Agda's disjoint ranges omit inter-token whitespace; the catalog
        # deliberately preserves those intervals instead of inventing an envelope.
        expected = "phaseOf(invertb)" if callee.startswith("ComputedIndex.phaseOf#") else "invertb"
        check(any(source_slice(l["source"]) == expected for l in call["sourceLinks"]),
              "nested call has no verified source-to-checked chain")
    direct_definitions = computed_module["sourceAlignment"]["definitions"]
    invert_alignment = next(d for d in direct_definitions if d["owner"].startswith("ComputedIndex.invert#"))
    check(invert_alignment["unavailable"] is None, "finite clause alignment is unavailable")
    for link in invert_alignment["links"]:
        locator = link["checked"]
        if locator["root"] == "compiled" and link["rule"] == "source.direct-first-order":
            root = next(r["value"] for r in trace["templateRoots"] if r["owner"] == locator["owner"] and r["root"] == "compiled")
            value = root
            for step in locator["path"]:
                value = value[step]
            check(source_slice(link["source"]) == value["symbol"].split("#")[0].rsplit(".", 1)[1],
                  "source order was confused with compiled constructor order")

    for name in ("ComputedIndex.nextPhase", "ComputedIndex.invert", "ComputedIndex.phaseOf"):
        expression_targets = [t for t in trace["targetOccurrences"] if t["owner"].startswith(name + "#") and t["role"] != "calculation"]
        check(expression_targets and all(t["sourcePrecision"] == "derived" for t in expression_targets), "explicit direct body lacks full source derivations: " + name)
        calculation = next(t for t in trace["targetOccurrences"] if t["owner"].startswith(name + "#") and t["role"] == "calculation")
        check(calculation["sourcePrecision"] == "derived", "aligned explicit signature did not complete calculation provenance")
        signature_alignment = next(s for s in computed_module["sourceAlignment"]["signatures"] if s["owner"] == calculation["owner"])
        check(signature_alignment["unavailable"] is None and any(l["checked"]["path"] == [] for l in signature_alignment["links"]), "missing complete signature alignment")
    make_signature = next(s for s in computed_module["sourceAlignment"]["signatures"] if s["owner"].startswith("ComputedIndex.make#"))
    check(make_signature["unavailable"] is None and any(l["bindings"] for l in make_signature["links"]), "explicit dependent signature lost its resolved binder")
    step_signature = next(s for s in computed_module["sourceAlignment"]["signatures"] if s["owner"].startswith("ComputedIndex.step#"))
    step_body = next(d for d in computed_module["sourceAlignment"]["definitions"] if d["owner"] == step_signature["owner"])
    check(step_signature["unavailable"] is None and step_body["unavailable"] is not None and not step_body["links"],
          "signature alignment promoted unsupported body elaboration")
    observe_signature = next(s for s in computed_module["sourceAlignment"]["signatures"] if s["owner"].startswith("ComputedIndex.observe#"))
    check(observe_signature["unavailable"] is not None and not observe_signature["links"], "hidden signature binders were admitted")

    check(computed["complete"] and all(o["status"] == "discharged" for o in computed["obligations"]),
          "computed finite indices did not generate completely")
    def computed_carrier(name):
        return next(c for c in computed["algebraicCarriers"] if c["symbol"].startswith(name + "#"))
    def computed_target(name):
        return next(o["target"] for o in computed["obligations"]
                    if o["symbol"].startswith(name + "#") and o["target"] is not None)
    event_index = computed_carrier("ComputedIndex.Event")
    packet_index = computed_carrier("ComputedIndex.Packet")
    evidence_index = computed_carrier("SpecializedIndexed.Evidence")
    state_index = computed_carrier("ComputedIndex.State")
    check("ComputedIndex.nextPhase" in event_index["constructors"][0]["resultIndices"][0]
          and "ComputedIndex.invert" in event_index["constructors"][0]["payload"][1]["refinements"][0],
          "computed constructor indices were erased")
    check(any(c["symbol"].startswith("ComputedIndex.select#")
              and any(d["symbol"].startswith("ComputedIndex.invert#") for d in c["callees"])
              for c in computed["calculationDependencies"]),
          "type-only computed helper dependency missing")
    expressions = []
    for enabled, opposite, phase, other in (("false", "true", "active", "idle"),
                                            ("true", "false", "idle", "active")):
        phase_value = f"'Indexed.Phase'::'Indexed.Phase.{phase}'"
        other_phase = f"'Indexed.Phase'::'Indexed.Phase.{other}'"
        marker = flag_value(opposite, opposite)
        event = sum_value(event_index, "event", [enabled, marker], [phase_value])
        wrong_result = sum_value(event_index, "event", [enabled, marker], [other_phase])
        wrong_member = sum_value(event_index, "event", [enabled, flag_value(enabled, enabled)], [phase_value])
        expressions += [f"'ComputedIndex.invert'({enabled})", opposite,
                        f"'ComputedIndex.nextPhase'({enabled}) == {phase_value}", "true",
                        f"{event_index['admissibility']}({event})", "true",
                        f"{event_index['admissibility']}({wrong_result})", "false",
                        f"{event_index['admissibility']}({wrong_member})", "false",
                        f"'ComputedIndex.observe'({phase_value}, {event})", opposite]
        for datum in ("false", "true"):
            evidence = indexed_value(evidence_index, "on" if opposite == "true" else "off", opposite, datum)
            packet = record_value(packet_index, [enabled, evidence])
            wrong_packet = record_value(packet_index, [opposite, evidence])
            state = record_value(state_index, [packet, event])
            expressions += [f"{packet_index['admissibility']}({packet})", "true",
                            f"{packet_index['admissibility']}({wrong_packet})", "false",
                            f"{computed_target('ComputedIndex.readPacket')}({packet})", datum,
                            f"{state_index['admissibility']}({state})", "true" if enabled == "false" else "false"]
    subprocess.run([java, "--class-path", str(validator / "jupyter-sysml-kernel-0.58.0-all.jar"),
                    str(repository / "test/TargetEvaluation.java"), str(validator / "sysml.library"),
                    str(work / "computed-index/model.sysml"), *expressions], check=True)

    relation = work / "contracts/relational.yaml"
    run("inspect", relation, work / "relational-inventory", 0)
    relation_inventory = json.loads((work / "relational-inventory/inventory.json").read_text())
    check(relation_inventory["resolutions"][0]["validation"]["encoding"] == "relation",
          "relation adapter was not selected")
    guarded = work / "contracts/guarded.yaml"
    run("inspect", guarded, work / "guarded-inventory", 0)
    run("generate", guarded, work / "guarded-diagnostic", 2, "--diagnostic")
    guarded_inventory = json.loads((work / "guarded-diagnostic/inventory.json").read_text())
    check_source_catalog(guarded_inventory)
    guarded_module = next(m for m in guarded_inventory["modules"] if m["name"] == "Guarded")
    guarded_alignment = next(d for d in guarded_module["sourceAlignment"]["definitions"] if d["owner"].startswith("Guarded.step#"))
    check(guarded_alignment["unavailable"] == "source-with-rewrite-unavailable" and not guarded_alignment["links"],
          "with expansion fabricated a direct source origin")
    check(any(a["contextOwner"] is not None and a["unavailable"] == "compiler-generated-origin-unresolved"
              for a in guarded_module["sourceCorrespondence"]["declarationAnchors"]),
          "generated helper parent was promoted into an exact source anchor")
    diagnostic = json.loads((work / "guarded-diagnostic/manifest.json").read_text())
    check(not diagnostic["complete"], "unsupported behavior claimed completion")
    report = json.loads((work / "guarded-diagnostic/correspondence.json").read_text())
    check(any(x["kind"] == "behavior" and x["status"] == "textual" for x in report["obligations"]),
          "missing executable-behavior boundary")

    problems = json.loads((work / "guarded-diagnostic/diagnostics.json").read_text())["diagnostics"]
    textual = {(x["symbol"], x["kind"]): x for x in report["obligations"] if x["status"] == "textual"}
    check(len(problems) == len(textual), "rule failures inflated unresolved-obligation accounting")
    allowed_codes = {"unsupported-syntax", "unsupported-semantics", "unsupported-target-representation"}
    for problem in problems:
        obligation = textual[(problem["symbol"], problem["kind"])]
        check(problem["code"] in allowed_codes and problem["code"] == obligation["reasonCode"],
              "translation refusal lacks a consistent category")
        check(problem["source"] == obligation["source"] and problem["source"]["symbol"],
              "classified refusal lost checked source links")
        check(problem["models"] == ["guarded"], "classified refusal lost its model")
        check(problem["message"] == obligation["reason"], "classified refusal lost its explanation")
        for cause in problem["causes"]:
            check(cause["code"] in allowed_codes and cause["rule"] and cause["message"],
                  "rule alternative lacks its own category or explanation")
    check(report["coverage"]["requiredObligations"] - report["coverage"]["dischargedObligations"] == len(problems),
          "classification changed completeness accounting")
    run("generate", guarded, work / "guarded-strict", 2)
    strict_problems = json.loads((work / "guarded-strict/diagnostics.json").read_text())
    check(strict_problems == json.loads((work / "guarded-diagnostic/diagnostics.json").read_text()),
          "strict mode changed refusal classification")

    expressions = []
    for x in (False, True):
        expressions += [f"'Agda2SysML.Foundation.not'({str(x).lower()})", str(not x).lower()]
        for y in (False, True):
            expressions += [f"'Agda2SysML.Foundation._∧_'({str(x).lower()}, {str(y).lower()})",
                            str(x and y).lower()]
    subprocess.run([java, "--class-path", str(validator / "jupyter-sysml-kernel-0.58.0-all.jar"),
                    str(repository / "test/TargetEvaluation.java"), str(validator / "sysml.library"),
                    str(outputs[0] / "model.sysml"), *expressions], check=True)
    print("CLI artifacts, reproducibility, mapping refusals, provenance, carrier/helper specialization, and target evaluation passed")
